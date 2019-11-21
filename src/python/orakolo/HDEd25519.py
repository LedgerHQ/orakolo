from ecpy.curves import Curve,Point

import hmac
import hashlib
import binascii
import unicodedata


"""
 OS CALL:
 
    void           os_perso_derive_node_bip32_seed_key(unsigned int mode, 
                                                       cx_curve_t curve, 
                                                       const unsigned int* path, unsigned int pathLength,  
                                                       unsigned char *privateKey, 
                                                       unsigned char* chain , 
                                                       unsigned char* seed_key, unsigned int seed_key_length);

    input:
      mode            = 0
      curve           = CX_CURVE_Ed25519
      path            = {0,1,2}
      path_length     = 3
      seed_key        = NULL
      seed_key_length = 0

    output:
      privatekey: 64 bytes
      chain: 32 bytes

    process:
      Step 1: retrieve the 512 bits master seed from bip39/bip32 24 words 
      Step 2: apply SLIP10 initialization to derive master Ed25519 key and chain code
      Step 3: Apply "BIP32-Ed25519 Hierarchical Deterministic Keys over a Non-linear Keyspace" paper from Dmitry Khovratovich and Jason Law



OS/Python Equivalence:
    OS:
       privateKey, chain <-          os_perso_derive_node_bip32(            CX_CURVE_Ed25519, path, path_len, privateKey, chain);
       privateKey, chain <- os_perso_derive_node_bip32_seed_key(HDW_NORMAL, CX_CURVE_Ed25519, path, path_len, privateKey, chain, seed, seed_length);
    Python:
       privateKey, public_key, chain <-BIP32Ed25519.derive_seed(                              path,                              seed)


    where seed is the BIP39/pbkdf2 mnemonic derivation

"""


TRACE=False
def trace(x):
    if (TRACE):
        print(x)

def _crypto_scalarmult_curve25519_base(k):
        cv25519 = Curve.get_curve("Ed25519")
        k = int.from_bytes(k, 'little')
        P = k*cv25519.generator
        return cv25519.encode_point(P)

ed25519_n = 2**252 + 27742317777372353535851937790883648493

def _NFKDbytes(str):
    return  unicodedata.normalize('NFKD', str).encode()

def _h512(m):
    return hashlib.sha512(m).digest()

def _h256(m):
    return hashlib.sha256(m).digest()

def _Fk(message, secret):
    return hmac.new(secret, message, hashlib.sha512).digest()

def _Fk256(message, secret):
    return hmac.new(secret, message, hashlib.sha256).digest()

def _get_bit(character, pattern):
    return character & pattern

def _set_bit(character, pattern):
    return character | pattern

def _clear_bit(character, pattern):
    return character & ~pattern

class BIP32Ed25519:

    def __init__(self):
        pass

    def root_key_slip10(self, master_secret):
        """
        INPUT: 
          S: 512 bits seed from BIP39/BIP32
          seedkey:"ed25519 seed"

        OUTPUT: 
          k = (kL,kR), c

        PROCESS:
          1. compute c = HMAC-SHA256(key=seedkey,0x01 || Data = S)
          2. compute I = HMAC-SHA512(key=seedkey, Data=S)
          3. split I = into tow sequence of 32-bytes sequence kL,Kr
          4. if the third highest bit of the last byte ok kL is not zero:
             S = I
             goto step 1
          5. Set the bits in kL as follows: 
               - the lowest 3 bits of the first byte of kL of are cleared
               - the highest bit of the last byte is cleared
               - the second highest bit of the last byte is set
          6. return (kL,kR), c  
        """
        trace("ENTER root_key_slip10")
        key=b'ed25519 seed'
        # root chain code
        c = bytearray(_Fk256(b'\x01'+master_secret, key))
        #KL:KR
        I = bytearray(_Fk(master_secret, key))
        kL, kR = I[:32], I[32:]
        while  _get_bit(kL[31], 0b00100000) != 0:
            master_secret = I
            I = bytearray(_Fk(master_secret, key))
            kL, kR = I[:32], I[32:]
        # the lowest 3 bits of the first byte of kL of are cleared
        kL[0]  = _clear_bit( kL[0], 0b00000111)
        # the highest bit of the last byte is cleared
        kL[31] = _clear_bit(kL[31], 0b10000000)
        # the second highest bit of the last byte is set
        kL[31] =   _set_bit(kL[31], 0b01000000)

        # root public key
        A = _crypto_scalarmult_curve25519_base(bytes(kL))
        
        trace("root key: ")
        trace("kL %s"%binascii.hexlify(kL))
        trace("kR %s"%binascii.hexlify(kR))
        trace("A  %s"%binascii.hexlify(A))
        trace("c  %s"%binascii.hexlify(c))
        trace("LEAVE root_key_slip10")
        return ((kL, kR), A, c)

    def public_child_key_not_hardened(self, node, i):
        """
        INPUT:
          A      : 32 bytes public key (y coordinatte only)
          c      : 32 bytes chain code
          i      : child index to compute (must not be hardened < 0x80000000)

        OUTPUT:
          A_i        : 32 bytes ith-child public key, A_i = kR_i.G (y coordinatte only)
          c_i        : 32 bytes ith-child chain code

        PROCESS:
          1. encode i 4-bytes little endian, il = encode_U32LE(i)
          2. if i is more than 2^31 this means it's a hardened path and it's no supported so None is returned
               - compute Z   = HMAC-SHA512(key=c, Data=0x02 | A | il )
               - compute c_  = HMAC-SHA512(key=c, Data=0x03 | A | il )
          3. ci = lowest_32bytes(c_)
          4. set ZL = highest_28bytes(Z)
          5. compute Ai
                Ai = A + ZL * 8 * G
          6. return Ai, c
        """

        trace("ENTER private_child_key")
        if not node:
            return None
        # unpack argument
        (AP, cP) = node

        assert 0 <= i < 2 ** 32

        trace("private_child_key/AP      : %s" % binascii.hexlify(AP))
        trace("private_child_key/cP      : %s" % binascii.hexlify(cP))
        trace("private_child_key/i       : %.04x" % i)

        # compute Z,c

        if i > 2 ** 31: #We only do none hardened paths
            return None

        i_bytes = i.to_bytes(4, 'little')

        # regular child
        trace("regular Z input           : %s" % binascii.hexlify(b'\x02' + AP + i_bytes))
        Z = _Fk(b'\x02' + AP + i_bytes, cP)
        trace("regular c input           : %s" % binascii.hexlify(b'\x03' + AP + i_bytes))
        c = _Fk(b'\x03' + AP + i_bytes, cP)[32:]

        cv25519 = Curve.get_curve("Ed25519")
        P = int.from_bytes(Z[:28], 'little') * 8 * cv25519.generator + cv25519.decode_point(AP)
        A = cv25519.encode_point(P)

        return (A, c)

    def private_child_key(self, node, i):
        """
        INPUT: 
          (kL,kR): 64 bytes private eddsa key
          A      : 32 bytes public key (y coordinatte only), optionnal as A = kR.G (y coordinatte only)
          c      : 32 bytes chain code
          i      : child index to compute (hardened if >= 0x80000000)

        OUTPUT: 
          (kL_i,kR_i): 64 bytes ith-child private eddsa key
          A_i        : 32 bytes ith-child public key, A_i = kR_i.G (y coordinatte only)
          c_i        : 32 bytes ith-child chain code

        PROCESS:
          1. encode i 4-bytes little endian, il = encode_U32LE(i)
          2. if i is less than 2^31
               - compute Z   = HMAC-SHA512(key=c, Data=0x02 | A | il )
               - compute c_  = HMAC-SHA512(key=c, Data=0x03 | A | il )
             else
               - compute Z   = HMAC-SHA512(key=c, Data=0x00 | kL | kR | il )
               - compute c_  = HMAC-SHA512(key=c, Data=0x01 | kL | kR | il )
          3. ci = lowest_32bytes(c_)
          4. set ZL = highest_28bytes(Z) 
             set ZR = lowest_32bytes(Z)
          5. compute kL_i:
                zl_  = LEBytes_to_int(ZL)
                kL_  = LEBytes_to_int(kL)
                kLi_ = zl_*8 + kL_
                if kLi_ % order == 0: child does not exist                
                kL_i = int_to_LEBytes(kLi_)                
          6. compute kR_i
                zr_  = LEBytes_to_int(ZR)
                kR_  = LEBytes_to_int(kR)
                kRi_ = (zr_ + kRn_) % 2^256
                kR_i = int_to_LEBytes(kRi_)
          7. compute A
                A = kLi_.G
          8. return (kL_i,kR_i), A_i, c  
        """

        trace("ENTER private_child_key")
        if not node:
            return None
        # unpack argument
        ((kLP, kRP), AP, cP) = node
        assert 0 <= i < 2**32

        i_bytes = i.to_bytes(4, 'little')
        trace("private_child_key/kLP     : %s"%binascii.hexlify(kLP))
        trace("private_child_key/kRP     : %s"%binascii.hexlify(kRP))
        trace("private_child_key/AP      : %s"%binascii.hexlify(AP))
        trace("private_child_key/cP      : %s"%binascii.hexlify(cP))
        trace("private_child_key/i       : %.04x"%i)

        #compute Z,c
        if i < 2**31:
            # regular child
            trace("regular Z input           : %s"%binascii.hexlify(b'\x02' + AP + i_bytes))
            Z = _Fk(b'\x02' + AP + i_bytes, cP)
            trace("regular c input           : %s"%binascii.hexlify(b'\x03' + AP + i_bytes))
            c = _Fk(b'\x03' + AP + i_bytes, cP)[32:]
        else:
            # harderned child
            trace("harderned Z input     : %s"%binascii.hexlify(b'\x00' + (kLP + kRP) + i_bytes))
            Z = _Fk(b'\x00' + (kLP + kRP) + i_bytes, cP)
            trace("harderned c input     : %s"%binascii.hexlify(b'\x01' + (kLP + kRP) + i_bytes))
            c = _Fk(b'\x01' + (kLP + kRP) + i_bytes, cP)[32:]
        trace("private_child_key/Z       : %s"%binascii.hexlify(Z))
        trace("private_child_key/c       : %s"%binascii.hexlify(c))

        ZL, ZR = Z[:28], Z[32:]
        trace("private_child_key/ZL      : %s"%binascii.hexlify(ZL))
        trace("private_child_key/ZR      : %s"%binascii.hexlify(ZR))

        #compute KLi
        trace("private_child_key/ZLint   : %x"%int.from_bytes(ZL, 'little'))
        trace("private_child_key/kLPint  : %x"%int.from_bytes(kLP, 'little'))
        kLn = int.from_bytes(ZL, 'little') * 8 + int.from_bytes(kLP, 'little')
        trace("private_child_key/kLn     : %x"%kLn)
        
        if kLn % ed25519_n == 0:
            return None

        #compute KRi
        trace("private_child_key/ZRint   : %x"%int.from_bytes(ZR, 'little'))
        trace("private_child_key/kRPint  : %x"%int.from_bytes(kRP, 'little'))
        kRn = (
            int.from_bytes(ZR, 'little') + int.from_bytes(kRP, 'little')
        ) % 2**256
        trace("private_child_key/kRn     : %x"%kRn)

        kL = kLn.to_bytes(32, 'little')
        kR = kRn.to_bytes(32, 'little')
        trace("private_child_key/kL      : %s"%binascii.hexlify(kL))
        trace("private_child_key/kR      : %s"%binascii.hexlify(kR))

        #compue Ai
        A =_crypto_scalarmult_curve25519_base(kL)
        trace("private_child_key/A       : %s"%binascii.hexlify(A))

        trace("LEAVE private_child_key")
        return ((kL, kR), A, c)


    def mnemonic_to_seed(self, mnemonic, passphrase='', prefix=u'mnemonic'):  
        """
        INPUT:  
           mnemonic: BIP39 words
           passphrase: optional passphrase
           prefix: optional prefix

        OUTPUT:
           512bits seed

        PROCESS:
           1. if passphrase not provided, set passphrase to empty string
           2. if prefix not provided, set prefix to empty string 'mnemonic'
           3. compute seed:
                - compute m_ = NFKD(mnemonic) 
                - compute p_ = NFKD(prefix | passphrase)
                - seed = PBKDF_SHA512(password=m_, salt=p_, round=2048)
           4. return 512bits seed

        """      
        seed = hashlib.pbkdf2_hmac('sha512', _NFKDbytes(mnemonic), _NFKDbytes(prefix+passphrase), 2048)
        return seed



    def derive_seed(self, path, seed):
        """
        INPUT:
           path: string path to derive (eg 42'/1/2)
           seed: 512 bits seed (eg: 512bits from BIP39 words)

        OUTPUT
           kL,kR : 64bytes private EDDSA key
           c     : 32 bytes chain code
        """
        trace("Compute path  %s"%path)
        trace("Compute mster %s"%seed)
        root = self.root_key_slip10(seed)
        node = root
        for i in path.split('/'):
            if i.endswith("'"):
                i = int(i[:-1]) + 2**31
            else:
                i = int(i)

            node = self.private_child_key(node, i)
            ((kLP, kRP), AP, cP) = node
            trace("Node %d"%i)
            trace("  kLP:%s" % binascii.hexlify(kLP))
            trace("  kRP:%s" % binascii.hexlify(kRP))
            trace("   AP:%s" % binascii.hexlify(AP))
            trace("   cP:%s" % binascii.hexlify(cP))
        return node

    def derive_mnemonic(self, path, mnemonic, passphrase='', prefix=u'mnemonic'):
        """
        INPUT:
           path: string path to derive (eg 42'/1/2)
           mnemonic: BIP39 words
           passphrase: optional passphrase
           prefix: optional prefix

        OUTPUT
           kL,kR : 64bytes private EDDSA key
           c     : 32 bytes chain code
        """
        seed = self.mnemonic_to_seed(mnemonic, passphrase, prefix)
        return self.derive_seed(path, seed)

if __name__ == "__main__":

    bip32ed25519 = BIP32Ed25519()

    for path in (u"42'/1/2", u"42'/3'/5"):
        print("*************************************")
        print("CHAIN: %s"%path)
        print()
        node = bip32ed25519.derive_mnemonic(path, u'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about')
        ((kL, kR), A, c) = node
        print("  kL:%s" % binascii.hexlify(kL))
        print("  kR:%s" % binascii.hexlify(kR))
        print("   c:%s" % binascii.hexlify(c))
        print("   A:%s" % binascii.hexlify(A))
        print()
        print()

    for path in ((u"42'", u"1/2"), (u"42'/3'", u"5")):
        print("*************************************")
        print()
        node = bip32ed25519.derive_mnemonic(path[0], u'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about')
        ((kL, kR), A, c) = node

        node = (A, c)

        for i in path[1].split('/'):
            i = int(i)
            node = bip32ed25519.public_child_key_not_hardened(node, i)

            (A, c) = node

            print("   c:%s" % binascii.hexlify(c))
            print("   A:%s" % binascii.hexlify(A))
            print()
            print()
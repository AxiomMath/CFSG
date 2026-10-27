module

public import Certificates.Data.Kernel.SmithL6K

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6

@[expose] def sumRowK (B w0 m0 : Nat) : List Nat → List Nat → Bool
  | w :: W, m :: M => (atLeast4 (m0 &&& m) || !B.testBit (w0 ^^^ w)) && sumRowK B w0 m0 W M
  | _, _ => true

end CFSG.SmithL6.K

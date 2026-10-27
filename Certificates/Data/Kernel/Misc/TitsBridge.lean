module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.TitsBridge

open CFSG.KC.Enum CFSG.KS

@[expose] def digitsK (cs : List Char) : List Nat :=
  (cs.filter Char.isDigit).map fun c => c.toNat - '0'.toNat

@[expose] noncomputable def cmp4 (P : Nat) : Nat → List Nat → Bool
  | k, a :: b :: c :: d :: t =>
      (10 * (10 * (10 * (10 * 0 + a) + b) + c) + d) % 1755 == pg 11 (mask 11) P k &&
        cmp4 P (k + 1) t
  | k, [] => k == 1755
  | _, _ => false

@[expose] noncomputable def bridgeK (P : Nat) (cs : List Char) : Bool := cmp4 P 0 (digitsK cs)

end CFSG.KC.TitsBridge

end

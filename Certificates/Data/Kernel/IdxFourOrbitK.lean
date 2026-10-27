module

public import Certificates.Data.Kernel.IdxFourChainK

public section

namespace CFSG.KC.IF4O

open CFSG.KC.IF4C

@[expose] noncomputable def apW (SP : Nat) (w : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) c (fun e _ ih => ap12 (look SP e) ih) w

@[expose] noncomputable def allLt (n : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Nat.blt e n && ih) w

section
variable (SP VT PS n : Nat) (L : List Nat) (P : Nat → Bool)

@[expose] noncomputable def entOK (j : Nat) (e : List Nat) : Bool :=
  Nat.beq (fld PS (fld VT j)) j && !(memN (fld VT j) L) &&
    bif Nat.blt (nthD 0 e 1) n then
      Nat.blt (nthD 0 e 0) j &&
        Nat.beq (ap12 (look SP (nthD 0 e 1)) (fld VT (nthD 0 e 0))) (fld VT j)
    else
      allLt n (dropN 2 e) &&
        (P (fld VT j) || P (Nat.xor (fld VT j) (apW SP (dropN 2 e) (fld VT j))))

@[expose] noncomputable def entsOK (es : List (List Nat)) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih j => entOK SP VT PS n L P j e && ih (Nat.succ j)) es j

@[expose] noncomputable def blkOK (E : List (List Nat)) (c : Nat) : Bool :=
  entsOK SP VT PS n L P (takeN 128 (dropN (Nat.mul 128 c) E)) (Nat.mul 128 c)

end

@[expose] noncomputable def cntOK (E : List (List Nat)) (N : Nat) : Bool := Nat.beq (lenN E) N

end CFSG.KC.IF4O

end

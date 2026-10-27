module

public import Certificates.Data.Kernel.F2TriSep

public section

namespace CFSG.KC.F2FormId

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.F2W

@[expose] noncomputable def altK (d M : Nat) : Bool :=
  andB (Nat.beq (trK d M) M) (allN d fun i => notB (bit M (Nat.add (Nat.mul d i) i)))

@[expose] noncomputable def invQK (d Q A : Nat) : Bool :=
  altK d (Nat.xor (mulW d (mulW d (trK d A) Q) A) Q)

@[expose] noncomputable def fixSumK (d : Nat) (P : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Prod.rec (motive := fun _ => Nat) (fun M X =>
      Nat.xor (mulW d (Nat.xor M (idF d)) X) ih) e) P

end CFSG.KC.F2FormId

end

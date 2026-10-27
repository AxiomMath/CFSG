module

public import Certificates.Data.Kernel.Co1BBound

public section

namespace CFSG.KC.Co1BBoundN

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT CFSG.KC.Enum
  CFSG.KC.Co1BBound

@[expose] noncomputable def vmTn (nb : Nat) (TL : List Nat) (a x : Nat) : Nat :=
  nIf(Nat.blt a nb, vmF (nat_lit 24) (getL (nat_lit 0) TL a) x, nat_lit 0)

@[expose] noncomputable def slotKn (nb : Nat) (TL b : List Nat) (s : Nat × Nat) : Nat :=
  vmTn nb TL s.2 (getL (nat_lit 0) b s.1)

@[expose] noncomputable def fKn (nb : Nat) (TL b : List Nat) (F : List (Nat × Nat)) : Nat :=
  F.foldl (fun acc s => Nat.xor acc (slotKn nb TL b s)) (nat_lit 0)

@[expose] noncomputable def combKn (nb : Nat) (TL S : List Nat) (F x : Nat) : Nat :=
  S.foldl (fun acc a => Nat.xor acc (vmTn nb TL a x)) F

@[expose] noncomputable def condKn (nb : Nat) (XB : Nat → Nat) (TL : List Nat) (x : Nat)
    (c : List Nat) : Bool :=
  Nat.beq (typK XB (combKn nb TL c.tail.tail (c.tail.headD 0) x)) (c.headD 0)

@[expose] noncomputable def condsKn (nb : Nat) (XB : Nat → Nat) (TL : List Nat)
    (CF : List (List Nat)) (x : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (condKn nb XB TL x c) ih) CF

@[expose] noncomputable def storeKn (nb : Nat) (XB : Nat → Nat) (TL b : List Nat) (u : Nat)
    (conds : List (List Nat × List (Nat × Nat))) : List (List Nat) :=
  conds.map fun c => typK XB (combKn nb TL c.1 (fKn nb TL b c.2) u) :: fKn nb TL b c.2 :: c.1

@[expose] noncomputable def lvlChunkKn (nb : Nat) (XB : Nat → Nat) (TL : List Nat)
    (CF : List (List (List Nat))) (F : Nat → Nat) (CN : List (List Nat)) (n : Nat) : Bool :=
  Nat.beq (cntTabK (condsKn nb XB TL (CF.getD (Nat.div n 9) [])) F (Nat.mul 13 (Nat.mod n 9)) 13)
    (getL 0 (CN.getD (Nat.div n 9) []) (Nat.mod n 9))

end CFSG.KC.Co1BBoundN

end

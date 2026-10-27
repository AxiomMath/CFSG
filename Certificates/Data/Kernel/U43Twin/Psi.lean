module

public import Certificates.Data.Kernel.U43Pk.Cover

public section

namespace CFSG.KD.U43Twin

open CFSG.KC.Enum CFSG.KD.U43Pk

@[expose] noncomputable def qmE (a b c d e f g h : Nat) : Nat :=
  Nat.add (Nat.add (Nat.add (Nat.mul 27 (Nat.mod (Nat.add (Nat.mul a e) (Nat.mul b g)) 3))
    (Nat.mul 9 (Nat.mod (Nat.add (Nat.mul a f) (Nat.mul b h)) 3)))
    (Nat.mul 3 (Nat.mod (Nat.add (Nat.mul c e) (Nat.mul d g)) 3)))
    (Nat.mod (Nat.add (Nat.mul c f) (Nat.mul d h)) 3)

@[expose] noncomputable def qmK (m n : Nat) : Nat :=
  qmE (Nat.div m 27) (Nat.mod (Nat.div m 9) 3) (Nat.mod (Nat.div m 3) 3) (Nat.mod m 3)
    (Nat.div n 27) (Nat.mod (Nat.div n 9) 3) (Nat.mod (Nat.div n 3) 3) (Nat.mod n 3)

@[expose] noncomputable def qposK (S : Nat → Nat) (t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun v acc => nIf(Nat.beq (S v) t, v, acc)) 24

@[expose] noncomputable def psiRowK (L H : Nat → Nat) (M : Nat → Nat → Nat) (P Q a : Nat) : Bool :=
  strictB (L a) fun A => bAnd(rawValidK A, bAnd(rawValidK (H a), bAnd(commK A P, bAnd(commK A Q,
    allBlk 0 (fun b => bAnd(Nat.beq (nrmK (L (M a b))) (nrmK (mulK A (L b))), commK A (H b)))
      24))))

end CFSG.KD.U43Twin

end

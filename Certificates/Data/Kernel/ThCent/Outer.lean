module

public import Certificates.Data.Kernel.ThCent.Defs

public section

namespace CFSG.KC.ThCent

open CFSG.KC.Th CFSG.KC.Loop

@[expose] noncomputable def normMu (MU X : Nat) : Bool :=
  (fun XM => orB (Nat.beq XM (mul24 MU X))
      (orB (Nat.beq XM (mul24 (pw24 MU (nat_lit 2)) X)) (Nat.beq XM (mul24 (pw24 MU (nat_lit 4)) X))))
    (mul24 X MU)

@[expose] noncomputable def muOK (MU LT : Nat) : Bool :=
  andB (Nat.beq (pw24 MU (nat_lit 7)) ident24)
    (allBelow (nat_lit 14) (nat_lit 1) (fun c => normMu MU (DceS.let24 LT c)))

@[expose] noncomputable def jv2 (MU X : Nat) : Bool :=
  Nat.beq (mul24 X MU) (mul24 (pw24 MU (nat_lit 2)) X)

@[expose] noncomputable def noFix (CB : Nat → Nat) (X : Nat) : Bool :=
  allBelow (nat_lit 819) (nat_lit 13) (fun k => DceS.notB (commB (DceS.mat CB k) X))

@[expose] noncomputable def outerQ (CB : Nat → Nat) (MU o r X : Nat) : Bool :=
  andB (ordRank o r X) (andB (jv2 MU X) (noFix CB X))

@[expose] noncomputable def ojAt (EB : Nat → Nat) (MU o r lo i : Nat) : Bool :=
  (fun X => andB (ordRank o r X) (jv2 MU X)) (DceS.mat EB (Nat.add lo i))

@[expose] noncomputable def countOJ (EB : Nat → Nat) (MU o r lo n hi : Nat) : Nat :=
  sumBelow n hi (fun i => nIf(ojAt EB MU o r lo i, nat_lit 1, nat_lit 0))

@[expose] noncomputable def ojChunk (EB : Nat → Nat) (n MU o r : Nat) (OJ : List Nat) (i : Nat) :
    Bool :=
  Nat.beq (countOJ EB MU o r (Nat.mul (nat_lit 2048) i) (cLen n i) (nat_lit 32)) (getN OJ i)

@[expose] noncomputable def markOK (EB CB : Nat → Nat) (MU o r n : Nat) (MK : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih lb => (fun j k => (fun X =>
        andB (andB (Nat.ble lb j) (Nat.blt j n))
          (andB (andB (ordRank o r X) (jv2 MU X))
            (andB (andB (Nat.blt k (nat_lit 819)) (commB (DceS.mat CB k) X)) (ih (Nat.succ j)))))
        (DceS.mat EB j))
      (Nat.land e (nat_lit 65535)) (Nat.shiftRight e (nat_lit 16))) MK

end CFSG.KC.ThCent

end

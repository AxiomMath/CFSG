module

public import Certificates.Data.Kernel.SporSch.Co1Mat
public import Certificates.Data.Kernel.Spor.Co2Shape
public import Certificates.Data.Kernel.Spor.Mathieu

public section

namespace CFSG.KS.SporSch.Lift

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.M24 CFSG.KS.Co2Shape CFSG.KS.Mathieu

@[expose] noncomputable def repK (PR m : Nat) : Nat := pg (nat_lit 24) (nat_lit 16777215) PR m

@[expose] noncomputable def valK (PR z m : Nat) : Nat :=
  nIf(Nat.blt m (nat_lit 2300), repK PR m, Nat.xor z (repK PR (Nat.sub m (nat_lit 2300))))

@[expose] noncomputable def sideK (PR z H Q j : Nat) : Bool :=
  strictB (pg (nat_lit 12) (nat_lit 4095) Q j) (fun k => strictB (actK H (repK PR j)) (fun w =>
    bAnd(Nat.blt k (nat_lit 2300),
      bIf(Nat.beq w (valK PR z k), true, Nat.beq w (valK PR z (Nat.add k (nat_lit 2300)))))))

@[expose] noncomputable def incV (PR z : Nat) (Ms : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun m _ ih p => strictB (valK PR z m) (fun v => bAnd(Nat.ble p v, ih (Nat.succ v)))) Ms

@[expose] noncomputable def liftK (PR Q0 Q1 H0 H1 z : Nat) (Ms : List Nat) : Bool :=
  bAnd(Nat.blt z (nat_lit 16777216),
  bAnd(Nat.beq (lenN Ms) (nat_lit 4600),
  bAnd(distinctL (nat_lit 4600) Ms (nat_lit 0),
  bAnd(incV PR z Ms (nat_lit 0),
    allN (nat_lit 2300) (fun j => bAnd(sideK PR z H0 Q0 j, sideK PR z H1 Q1 j))))))

end CFSG.KS.SporSch.Lift

end

module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.SporSch.RuK

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Text

@[expose] noncomputable def hexPack (wd bd cnt start len w F : Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool)
    (fun e t _ acc => bAnd(Nat.beq e cnt, bAnd(Nat.beq t (nat_lit 0), Nat.beq acc F)))
    (fun ch _ ih e t v acc => strictB (hexV (Char.toNat ch)) (fun h => bIf(Nat.blt h (nat_lit 16),
      strictB (Nat.add (Nat.mul v (nat_lit 16)) h) (fun v' =>
        bIf(Nat.beq (Nat.succ t) wd,
          bIf(Nat.blt v' bd,
            strictB (nIf(bAnd(Nat.ble start e, Nat.blt e (Nat.add start len)),
                Nat.lor acc (Nat.shiftLeft v' (Nat.mul w (Nat.sub e start))), acc))
              (fun acc' => ih (Nat.succ e) (nat_lit 0) (nat_lit 0) acc'), false),
          ih e (Nat.succ t) v' acc)),
      false)))
    cs

@[expose] noncomputable def hexPackK (wd bd cnt start len w F : Nat) (cs : List Char) : Bool :=
  bAnd(Nat.blt (nat_lit 0) wd,
    hexPack wd bd cnt start len w F cs (nat_lit 0) (nat_lit 0) (nat_lit 0) (nat_lit 0))

@[expose] noncomputable def posK (n m w F POS : Nat) : Bool :=
  bAnd(allN m (fun i => strictB (pg w (mask w) F i) (fun x =>
      bAnd(Nat.blt x n, Nat.beq (pg w (mask w) POS x) i))),
    allN n (fun x => strictB (pg w (mask w) POS x) (fun p =>
      bIf(Nat.beq p n, true, bAnd(Nat.blt p m, Nat.beq (pg w (mask w) F p) x)))))

@[expose] noncomputable def resK (m w w' F POS G R : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight R (Nat.mul m w')) (nat_lit 0),
    allN m (fun i => Nat.beq (pg w' (mask w') R i)
      (pg w (mask w) POS (pg w (mask w) G (pg w (mask w) F i)))))

@[expose] noncomputable def row2K (n w m : Nat) (nw : Nat) (LR TR : Nat → Nat) (pK : Nat → Bool)
    (a : Nat) : Bool :=
  strictB (LR (nat_lit 0)) (fun R0 => strictB (LR (nat_lit 1)) (fun R1 =>
  strictB (TR (Nat.add (roff n nw R0) a)) (fun T0 => strictB (roff n nw R1) (fun o1 =>
    allN (rcnt R1) (fun b => strictB (pcomp n w m T0 (TR (Nat.add o1 b))) pK)))))

end CFSG.KS.SporSch

end

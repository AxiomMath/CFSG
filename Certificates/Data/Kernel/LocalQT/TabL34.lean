module

public import Certificates.Data.Kernel.LocalQT.TabA2

public section

namespace CFSG.KS.TabL34

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.TabA2

@[expose] noncomputable def cgK (ST CG : Nat → Nat) (R kC cnt : Nat) : Bool :=
  allN kC (fun c => bAnd(Nat.blt (CG c) cnt,
    Nat.beq (pc (ST (CG c)) R) (pc R (ST (CG c)))))

@[expose] noncomputable def centK (ST CG : Nat → Nat) (R kC X : Nat) : Bool :=
  bIf(Nat.beq X idn, true, bIf(Nat.beq X R, true,
    anyK kC (fun c => strictB (ST (CG c)) (fun Y =>
      bIf(Nat.beq (pc X Y) (pc Y X), false, true)))))

@[expose] noncomputable def twK (ST TW : Nat → Nat) (R cnt k : Nat) : Bool :=
  strictB (ST k) (fun U => bIf(bAnd(Nat.beq (pc U R) (pc R U),
      bAnd(Nat.beq (pc U U) idn, bIf(Nat.beq U idn, false, true))),
    strictB (TW k) (fun y => bAnd(Nat.blt y cnt, strictB (ST y) (fun Y =>
      strictB (pinv Y) (fun YI => bAnd(invOK Y YI, Nat.beq (pc (pc YI R) Y) (pc R U)))))), true))

@[expose] noncomputable def rsK (G T PL POS SRT SRI ST CG : Nat → Nat) (R kC cnt lo len : Nat) :
    Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i cnt,
    bAnd(penumPtK (nat_lit 42) (nat_lit 6) (mask 6) (nat_lit 252) false G G (nat_lit 6) cnt
      T PL POS SRT SRI i, centK ST CG R kC (T i)), true)))

@[expose] noncomputable def tsK (ST TW : Nat → Nat) (R cnt lo len : Nat) : Bool :=
  allN len (fun d => strictB (Nat.add lo d) (fun i => bIf(Nat.blt i cnt, twK ST TW R cnt i, true)))

end CFSG.KS.TabL34

end

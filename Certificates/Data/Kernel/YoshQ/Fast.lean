module

public import Certificates.Data.Kernel.YoshQ.Idx

public section

namespace CFSG.KC.YoshQ

open CFSG.KC.Enum CFSG.KS CFSG.EvenSporadicStandard.M12Std.Yosh

@[expose] noncomputable def hN (P x : Nat) : Nat := x % 2 ^ (16 * 5) % P

@[expose] noncomputable def hmaskF (P : Nat) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun M => M)
    (fun x _ ih M => strictN (M ||| (1 <<< hN P x)) ih) L

@[expose] noncomputable def hmask (P : Nat) (L : List Nat) : Nat := hmaskF P L 0

@[expose] noncomputable def memH (P : Nat) (L : List Nat) (x : Nat) : Bool :=
  (hmask P L).testBit (hN P x)

@[expose] noncomputable def cjW (cnt EP t₁ t₂ j : Nat) : Bool :=
  Nat.blt j cnt && eqN 16 5 (cjN 16 5 (fldN EP (16 * 5) j) t₁) t₂

@[expose] noncomputable def posW (cnt EP : Nat) (GS : List Nat) (reps : List (List (Fin 9 × Bool)))
    (T c : Nat) : Bool :=
  Nat.blt (c / 4096) reps.length && cjW cnt EP (nTN GS (reps.getD (c / 4096) [])) T (c % 4096)

@[expose] noncomputable def l6V (cnt EP P : Nat) (NL good : List Nat) (e : Nat) (LE : List Nat)
    (j : Nat) (W : List Nat) : Bool :=
  Nat.blt j LE.length &&
    Nat.beq (NL.filter (ctN 16 5 (LE.getD j 0))).length 128 &&
    Nat.ble LE.length W.length &&
    (LE.zip W).all fun p => !memH P good p.1 ||
      cjW cnt EP (cond (Nat.beq (p.2 % 2) 0) e (LE.getD j 0)) p.1 (p.2 / 2)

@[expose] noncomputable def l7fV (cnt EP P : Nat) (GS NL : List Nat) (α k e u : Nat)
    (LE W V : List Nat) (cu cue : Nat) : Bool :=
  Nat.ble LE.length W.length && Nat.ble LE.length V.length &&
    (LE.zip V).all (fun p => !memH P (goodTabsN GS NL α k) p.1 ||
      posW cnt EP GS (goodRepsN GS NL α k) p.1 p.2) &&
    (LE.filter (memH P (goodTabsN GS NL α k))).length == 56 &&
    posW cnt EP GS (goodRepsN GS NL α k) u cu &&
    posW cnt EP GS (goodRepsN GS NL α k) (pmN 16 5 u e) cue &&
    memN 16 5 LE u && memN 16 5 LE (pmN 16 5 u e) && ctN 16 5 e u &&
    (LE.zip W).all fun p => !memH P (goodTabsN GS NL α k) p.1 ||
      cjW cnt EP (cond (Nat.beq (p.2 % 3) 0) e (cond (Nat.beq (p.2 % 3) 1) u (pmN 16 5 u e))) p.1
        (p.2 / 3)

@[expose] noncomputable def l7AV (cnt EP P : Nat) (GS NL : List Nat) (α k c : Nat)
    (GA LA LE LS V : List Nat) : Bool :=
  Nat.ble GA.length V.length &&
    (GA.zip V).all (fun p => posW cnt EP GS (badRepsN GS NL α k) p.1 p.2) &&
    LA.all (fun a => LA.all fun b => ctN 16 5 a b) &&
    LA.all (fun a => eqN 16 5 (pmN 16 5 a a) (pidn 16 5)) &&
    GA.all (memN 16 5 LE) &&
    LE.all (fun y => !memH P (badTabsN GS NL α k) y || memN 16 5 LA y) &&
    LS.all (fun y => !LA.all (commInN 16 5 c y) || memN 16 5 LE y) &&
    LS.all (fun y => !LA.all (ctN 16 5 y) || memN 16 5 LA y)

@[expose] noncomputable def goodV (cnt EP P : Nat) (GS NL : List Nat) (α k : Nat)
    (L V : List Nat) : Bool :=
  Nat.ble L.length V.length &&
    (L.zip V).all fun p => !memH P (goodTabsN GS NL α k) p.1 ||
      posW cnt EP GS (goodRepsN GS NL α k) p.1 p.2

@[expose] noncomputable def fusionCoverV (cnt EP P : Nat) (GS NL : List Nat) (α k : Nat)
    (V : List Nat) : Bool :=
  Nat.ble NL.length V.length &&
    (NL.zip V).all (fun p => (!memH P (goodTabsN GS NL α k) p.1 ||
        posW cnt EP GS (goodRepsN GS NL α k) p.1 p.2) &&
      (!involN 16 5 p.1 || memH P (goodTabsN GS NL α k) p.1 ||
        posW cnt EP GS (badRepsN GS NL α k) p.1 p.2)) &&
    (NL.filter (memH P (goodTabsN GS NL α k))).length == goodCount α

end CFSG.KC.YoshQ

end

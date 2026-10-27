module

public import Certificates.Data.Kernel.T75JM.N0K
public import CFSG.CGT.T75JM.PCheckInputs

public section

namespace CFSG.KC.N0K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75JM

@[expose] noncomputable def pw (L : Int → Nat) (w : List (Fin 6 × Bool)) : Nat :=
  wordK 22 5 idn L (lw w)

@[expose] noncomputable def pc (A B : Nat) : Nat := pcomp 22 5 (mask 5) A B

@[expose] noncomputable def ePk (L : Int → Nat) (i : Nat) : Nat := pw L (vExp (eWtab.getD i []))

@[expose] noncomputable def with8 (f : Nat → Nat) (k : (Nat → Nat) → Bool) : Bool :=
  strictB (f 0) fun p0 => strictB (f 1) fun p1 => strictB (f 2) fun p2 =>
  strictB (f 3) fun p3 => strictB (f 4) fun p4 => strictB (f 5) fun p5 =>
  strictB (f 6) fun p6 => strictB (f 7) fun p7 =>
  k fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3
    else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7
    else f i

@[expose] noncomputable def eMulK (E : Nat → Nat) : Bool :=
  decide (∀ c d : V3, Nat.beq (pc (E (idx3 c)) (E (idx3 d))) (E (idx3 (c + d))) = true)

@[expose] noncomputable def eInjK (E : Nat → Nat) : Bool :=
  nodupN ((List.range 8).map fun i => keyL (List.range 22) (E i))

@[expose] noncomputable def conjK (E : Nat → Nat) (V V' : Nat) (M : GL (Fin 3) (ZMod 2)) : Bool :=
  decide (∀ c : V3, Nat.beq (pc (pc V (E (idx3 c))) V') (E (idx3 (glAct M c))) = true)

@[expose] noncomputable def actGK (L : Int → Nat) (E : Nat → Nat) : Bool :=
  decide (∀ c : V3, Nat.beq (pw L (dExp (dW c))) (E (idx3 c)) = true ∧
    Nat.beq (pw L (thExp (dW c))) (E (idx3 (glAct mG c))) = true)

@[expose] noncomputable def pOkE (L : Int → Nat) (E : Nat → Nat) : Bool :=
  eMulK E && eInjK E &&
    Nat.beq (E 1) (pw L [(2, true), (3, true), (4, true)]) &&
    conjK E (pw L (vGen 0)) (pw L (invWord (vGen 0))) mV1 &&
    conjK E (pw L (vGen 1)) (pw L (invWord (vGen 1))) mV2 &&
    actGK L E &&
    Nat.beq (pw L (dExp uW)) (pw L (vExp wA)) && Nat.beq (pw L (thExp uW)) (pw L (vExp wB)) &&
    Nat.beq (pw L (vExp (sV ++ sV))) idn && Nat.beq (pw L (vExp (rV ++ rV ++ rV ++ rV))) idn &&
    Nat.beq (pw L (vExp (sV ++ rV ++ sV ++ rV))) idn &&
    conjK E (pw L (vExp sV)) (pw L (invWord (vExp sV))) mS &&
    conjK E (pw L (vExp rV)) (pw L (invWord (vExp rV))) mR

@[expose] noncomputable def pOkK (L : Int → Nat) : Bool :=
  withL L fun L => with8 (ePk L) (pOkE L)

@[expose] noncomputable def allAT (L : Int → Nat) (g : Nat → Nat → Nat → Nat → Bool) : Bool :=
  allW a6Words (fun a u => strictB (wordK 22 5 idn L (u.map a6Z)) fun A =>
    (List.range 16).all fun k => strictB (tk L k) (g a k A)) (nat_lit 0)

@[expose] noncomputable def comAt (A T e x : Nat) : Bool :=
  Nat.beq (fdN 5 A (fdN 5 T (fdN 5 e x))) (fdN 5 e (fdN 5 A (fdN 5 T x)))

@[expose] noncomputable def eqAt (A T P : Nat) : Bool :=
  (List.range 22).all fun x => Nat.beq (fdN 5 A (fdN 5 T x)) (fdN 5 P x)

@[expose] noncomputable def eCentE (L : Int → Nat) (E : Nat → Nat) : Bool :=
  allAT L fun _ _ A T =>
    !((List.range 22).all fun x => comAt A T (E 1) x && comAt A T (E 2) x && comAt A T (E 4) x) ||
      (List.range 8).any fun i => eqAt A T (E i)

@[expose] noncomputable def eCentK (L : Int → Nat) : Bool :=
  withL L fun L => with8 (ePk L) (eCentE L)

@[expose] def lin3 (c0 c1 c2 i : Nat) : Nat :=
  (if i % 2 = 1 then c0 else 0) ^^^ (if i / 2 % 2 = 1 then c1 else 0) ^^^
    (if i / 4 % 2 = 1 then c2 else 0)

@[expose] def affL : Fin 3 → Bool → Nat → Nat → Nat
  | 0, true, s, i => lin3 1 4 6 i ^^^ s
  | 0, false, s, i => lin3 1 6 2 (i ^^^ s)
  | 1, true, s, i => lin3 1 6 5 i ^^^ s
  | 1, false, s, i => lin3 1 7 5 (i ^^^ s)
  | 2, true, s, i => lin3 2 1 7 i ^^^ s
  | 2, false, s, i => lin3 2 1 7 (i ^^^ s)

@[expose] def sel3 (t0 t1 t2 : Nat) : Fin 3 → Nat
  | 0 => t0
  | 1 => t1
  | 2 => t2

@[expose] def evW (t0 t1 t2 : Nat) (w : List (Fin 3 × Bool)) (i : Nat) : Nat :=
  w.foldr (fun p y => affL p.1 p.2 (sel3 t0 t1 t2 p.1) y) i

@[expose] def eqW (t0 t1 t2 : Nat) (u v : List (Fin 3 × Bool)) : Bool :=
  (List.range 8).all fun i => evW t0 t1 t2 u i == evW t0 t1 t2 v i

@[expose] def finKW (ws : List (List (Fin 3 × Bool))) : Bool :=
  (List.range 8).all fun t0 => (List.range 8).all fun t1 => (List.range 8).all fun t2 =>
    !(pRs.all (fun r => eqW t0 t1 t2 r.1 r.2) &&
        ([0, 1, 2] : List (Fin 3)).all fun j =>
          (List.range 8).all fun i => evW t0 t1 t2 (pEw j) i == i ^^^ 2 ^ j.val) ||
      ws.all fun w => eqW t0 t1 t2 w []

@[expose] def finK : Bool := finKW pWords

abbrev AffOk : Prop := ∀ (k : Fin 3) (b : Bool) (c : V3) (i : Fin 8),
  ((if b then affPerm8 (mv k) c else (affPerm8 (mv k) c)⁻¹) i).val = affL k b (vecIdx c).val i.val

abbrev TrOk : Prop := ∀ (j : Fin 3) (i : Fin 8),
  (translate8 (Pi.single j 1) i).val = i.val ^^^ 2 ^ j.val

end CFSG.KC.N0K

end

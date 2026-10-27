module

public import Certificates.Data.Kernel.T75M23.N7K
public import CFSG.CGT.T75M23.P7CheckInputs

public section

namespace CFSG.KC.N7K

open CFSG.KC.Enum CFSG.KS CFSG.KC.TabWord CFSG.KC.Misc CFSG.CGT.T75M23
open CFSG.CGT.T75JM (V3 glAct affPerm8 translate8 vecIdx)

@[expose] noncomputable def pw (L : Int → Nat) (w : List (Fin 6 × Bool)) : Nat :=
  wordK 23 5 idn L (lw w)

@[expose] noncomputable def pc (A B : Nat) : Nat := pcomp 23 5 (mask 5) A B

@[expose] noncomputable def ePk (L : Int → Nat) (i : Nat) : Nat := pw L (vExp7 (eWtab7.getD i []))

@[expose] noncomputable def with8 (f : Nat → Nat) (k : (Nat → Nat) → Bool) : Bool :=
  strictB (f 0) fun p0 => strictB (f 1) fun p1 => strictB (f 2) fun p2 =>
  strictB (f 3) fun p3 => strictB (f 4) fun p4 => strictB (f 5) fun p5 =>
  strictB (f 6) fun p6 => strictB (f 7) fun p7 =>
  k fun i => if i = 0 then p0 else if i = 1 then p1 else if i = 2 then p2 else if i = 3 then p3
    else if i = 4 then p4 else if i = 5 then p5 else if i = 6 then p6 else if i = 7 then p7
    else f i

@[expose] noncomputable def eMulK (E : Nat → Nat) : Bool :=
  decide (∀ c d : V3, Nat.beq (pc (E (idx37 c)) (E (idx37 d))) (E (idx37 (c + d))) = true)

@[expose] noncomputable def eInjK (E : Nat → Nat) : Bool :=
  nodupN ((List.range 8).map fun i => keyL (List.range 23) (E i))

@[expose] noncomputable def conjK (E : Nat → Nat) (V V' : Nat) (M : GL (Fin 3) (ZMod 2)) : Bool :=
  decide (∀ c : V3, Nat.beq (pc (pc V (E (idx37 c))) V') (E (idx37 (glAct M c))) = true)

@[expose] noncomputable def actGK (L : Int → Nat) (E : Nat → Nat) : Bool :=
  decide (∀ (k : Fin 2) (c : V3), Nat.beq (pw L (dExp7 (dW7 c))) (E (idx37 c)) = true ∧
    Nat.beq (pw L (thExp7 k (dW7 c))) (E (idx37 (glAct mG7 c))) = true)

@[expose] noncomputable def pOkE (L : Int → Nat) (E : Nat → Nat) : Bool :=
  eMulK E && eInjK E &&
    Nat.beq (E 4) (pw L [(2, true), (5, true)]) &&
    conjK E (pw L (vGen7 0)) (pw L (invWord7 (vGen7 0))) mV17 &&
    conjK E (pw L (vGen7 1)) (pw L (invWord7 (vGen7 1))) mV27 &&
    actGK L E &&
    Nat.beq (pw L (dExp7 uW7)) (pw L (vExp7 wA7)) &&
    Nat.beq (pw L (thExp7 0 uW7)) (pw L (vExp7 wB7)) &&
    Nat.beq (pw L (d0W7 1)) (pw L (vExp7 wD07)) &&
    Nat.beq (pw L (vExp7 (sV7 ++ sV7))) (pw L []) &&
    Nat.beq (pw L (vExp7 (rV7 ++ rV7 ++ rV7 ++ rV7))) (pw L []) &&
    Nat.beq (pw L (vExp7 (sV7 ++ rV7 ++ sV7 ++ rV7))) (pw L []) &&
    conjK E (pw L (vExp7 sV7)) (pw L (invWord7 (vExp7 sV7))) mS7 &&
    conjK E (pw L (vExp7 rV7)) (pw L (invWord7 (vExp7 rV7))) mR7

@[expose] noncomputable def pOkK (L : Int → Nat) : Bool :=
  withL L fun L => with8 (ePk L) (pOkE L)

@[expose] noncomputable def allAT (L : Int → Nat) (g : Nat → Nat → Nat → Nat → Bool) : Bool :=
  allW a7Words (fun a u => strictB (wordK 23 5 idn L (u.map a7Z)) fun A =>
    (List.range 16).all fun k => strictB (tk L k) (g a k A)) (nat_lit 0)

@[expose] noncomputable def comAt (A T e x : Nat) : Bool :=
  Nat.beq (fdN 5 A (fdN 5 T (fdN 5 e x))) (fdN 5 e (fdN 5 A (fdN 5 T x)))

@[expose] noncomputable def eqAt (A T P : Nat) : Bool :=
  (List.range 23).all fun x => Nat.beq (fdN 5 A (fdN 5 T x)) (fdN 5 P x)

@[expose] noncomputable def eCentE (L : Int → Nat) (E : Nat → Nat) : Bool :=
  allAT L fun _ _ A T =>
    !((List.range 23).all fun x => comAt A T (E 1) x && comAt A T (E 2) x && comAt A T (E 4) x) ||
      (List.range 8).any fun i => eqAt A T (E i)

@[expose] noncomputable def eCentK (L : Int → Nat) : Bool :=
  withL L fun L => with8 (ePk L) (eCentE L)

@[expose] def lin3 (c0 c1 c2 i : Nat) : Nat :=
  (if i % 2 = 1 then c0 else 0) ^^^ (if i / 2 % 2 = 1 then c1 else 0) ^^^
    (if i / 4 % 2 = 1 then c2 else 0)

@[expose] def affL : Fin 3 → Bool → Nat → Nat → Nat
  | 0, true, s, i => lin3 2 1 4 i ^^^ s
  | 0, false, s, i => lin3 2 1 4 (i ^^^ s)
  | 1, true, s, i => lin3 5 7 4 i ^^^ s
  | 1, false, s, i => lin3 5 3 4 (i ^^^ s)
  | 2, true, s, i => lin3 7 4 2 i ^^^ s
  | 2, false, s, i => lin3 7 4 2 (i ^^^ s)

@[expose] def sel3 (t0 t1 t2 : Nat) : Fin 3 → Nat
  | 0 => t0
  | 1 => t1
  | 2 => t2

@[expose] def evW (t0 t1 t2 : Nat) (w : List (Fin 3 × Bool)) (i : Nat) : Nat :=
  w.foldr (fun p y => affL p.1 p.2 (sel3 t0 t1 t2 p.1) y) i

@[expose] def eqW (t0 t1 t2 : Nat) (u v : List (Fin 3 × Bool)) : Bool :=
  (List.range 8).all fun i => evW t0 t1 t2 u i == evW t0 t1 t2 v i

@[expose] def finKW (rs : List (List (Fin 3 × Bool) × List (Fin 3 × Bool)))
    (ws : List (List (Fin 3 × Bool))) : Bool :=
  (List.range 8).all fun t0 => (List.range 8).all fun t1 => (List.range 8).all fun t2 =>
    !(rs.all (fun r => eqW t0 t1 t2 r.1 r.2) &&
        ([0, 1, 2] : List (Fin 3)).all fun j =>
          (List.range 8).all fun i => evW t0 t1 t2 (pEw7 j) i == i ^^^ 2 ^ j.val) ||
      ws.all fun w => eqW t0 t1 t2 w []

abbrev AffOk : Prop := ∀ (k : Fin 3) (b : Bool) (c : V3) (i : Fin 8),
  ((if b then affPerm8 (mv7 k) c else (affPerm8 (mv7 k) c)⁻¹) i).val =
    affL k b (vecIdx c).val i.val

abbrev TrOk : Prop := ∀ (j : Fin 3) (i : Fin 8),
  (translate8 (Pi.single j 1) i).val = i.val ^^^ 2 ^ j.val

end CFSG.KC.N7K

end

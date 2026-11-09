module

public import Certificates.Data.Kernel.LocalQT.TcP

public section

namespace CFSG.KC.B45P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC

@[expose] noncomputable def tGenK (n w : Nat) (G GI : List Nat) (T TI S : Nat) (wd : List Int) :
    Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(permOK n w (mask w) (n * w) T TI,
    wordP n w (pidn n w) G GI wd fun A _ =>
      bAnd(Nat.beq A S, Nat.beq (pcomp n w (mask w) A T) (pcomp n w (mask w) T A)))))

@[expose] noncomputable def letGF (idn : Nat) (G GI : List Nat) (z : Int) (k : Nat → Bool) :
    Bool :=
  Int.rec (motive := fun _ => Bool)
    (fun m => Nat.rec (motive := fun _ => Bool) (k idn) (fun j _ => k (getTc idn G j)) m)
    (fun m => k (getTc idn GI m)) z

@[expose] noncomputable def wordF (n w idn : Nat) (G GI : List Nat) (wd : List Int)
    (k : Nat → Bool) : Bool :=
  List.rec (motive := fun _ => (Nat → Bool) → Bool) (fun k => k idn)
    (fun z _ ih k => ih fun A => letGF idn G GI z fun L =>
      strictB (pcomp n w (mask w) L A) k) wd k

@[expose] noncomputable def tGenF (n w : Nat) (G GI : List Nat) (T TI S : Nat) (wd : List Int) :
    Bool :=
  bAnd(idK n w (mask w), bAnd(gensTc n w G GI, bAnd(permOK n w (mask w) (n * w) T TI,
    wordF n w (pidn n w) G GI wd fun A =>
      bAnd(Nat.beq A S, Nat.beq (pcomp n w (mask w) A T) (pcomp n w (mask w) T A)))))

private theorem strictB_eqT (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem letGP_eq_letGF (idn : Nat) (G GI : List Nat) (z : Int) (k : Nat → Nat → Bool)
    (f : Nat → Bool) (h : ∀ L LI, k L LI = f L) : letGP idn G GI z k = letGF idn G GI z f := by
  cases z with
  | ofNat m =>
    cases m with
    | zero => exact h idn idn
    | succ j => exact h (getTc idn G j) (getTc idn GI j)
  | negSucc m => exact h (getTc idn GI m) (getTc idn G m)

theorem wordP_eq_wordF (n w idn : Nat) (G GI : List Nat) (wd : List Int) :
    ∀ (k : Nat → Nat → Bool) (f : Nat → Bool), (∀ A AI, k A AI = f A) →
      wordP n w idn G GI wd k = wordF n w idn G GI wd f := by
  induction wd with
  | nil => intro k f h; exact h idn idn
  | cons z rest ih =>
    intro k f h
    have hc : wordP n w idn G GI (z :: rest) k = wordP n w idn G GI rest (fun A AI =>
        letGP idn G GI z fun L LI => strictB (pcomp n w (mask w) L A) fun B =>
          strictB (pcomp n w (mask w) AI LI) fun BI => k B BI) := rfl
    have hf : wordF n w idn G GI (z :: rest) f = wordF n w idn G GI rest (fun A =>
        letGF idn G GI z fun L => strictB (pcomp n w (mask w) L A) f) := rfl
    rw [hc, hf]
    refine ih _ _ fun A AI => letGP_eq_letGF _ _ _ _ _ _ fun L LI => ?_
    simp only [strictB_eqT, h]

theorem tGenK_eq_tGenF (n w : Nat) (G GI : List Nat) (T TI S : Nat) (wd : List Int) :
    tGenK n w G GI T TI S wd = tGenF n w G GI T TI S wd := by
  unfold tGenK tGenF
  rw [wordP_eq_wordF n w (pidn n w) G GI wd _ (fun A =>
      bAnd(Nat.beq A S, Nat.beq (pcomp n w (mask w) A T) (pcomp n w (mask w) T A)))
    fun _ _ => rfl]

end CFSG.KC.B45P

end

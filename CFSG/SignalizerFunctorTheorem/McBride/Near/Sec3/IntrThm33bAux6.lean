module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux5
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33bAux2

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv Thm33a

@[expose] def Thm33bBelow.{v} (p n : ℕ) : Prop :=
  ∀ (Γ : Type v) [Group Γ] [Finite Γ] (A X Y : Subgroup Γ), Nat.card ↥X < n →
    NearAsolvAction p A X → (iPairsY A X Y).Nonempty → Concl A X Y

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X Y : Subgroup Γ}

theorem concl_step
    (ih : Thm33bBelow.{u} p (Nat.card ↥X)) (h : NearAsolvAction p A X)
    (hY : (iPairsY A X Y).Nonempty) : Concl A X Y := by
  obtain ⟨⟨X₁, X₂⟩, hP⟩ := hY
  by_cases hX' : kOf X ⊔ iThetaU A X Y = X
  · by_cases hN : ∃ N : Subgroup Γ, N ≤ X ∧ Admits X N ∧ Admits A N ∧
        N ⊓ cenIn X (A : Set Γ) ≤ Y ∧ N ≠ ⊥
    · obtain ⟨N, hNX, hXN, hAN, hND, hN1⟩ := hN
      refine concl_of_quotient h hP hNX hXN hAN hND ?_
      have hlt : Nat.card ↥(AChief.qimg N X) < Nat.card ↥X :=
        Thm211.card_qimg_lt hNX hXN hN1
      exact ih (AChief.QG N) (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) hlt
        (Thm211.nearAsolvAction_qimg h hXN hAN)
        ⟨_, qimg_mem_iPairsY h hP hXN hAN (inf_le_of_inf_dsub_le h hP hXN hAN hND)⟩
    · exact concl_of_key h ⟨_, hP⟩ hX'.symm fun N hNX hXN hAN hND =>
        by_contra fun hN1 => hN ⟨N, hNX, hXN, hAN, hND, hN1⟩
  · have hX'X : kOf X ⊔ iThetaU A X Y ≤ X := sup_le (kOf_le X) iThetaU_le
    have hDX' : cenIn X (A : Set Γ) ≤ kOf X ⊔ iThetaU A X Y :=
      (dsub_le_iThetaU hP).trans le_sup_right
    have hAK : Admits A (kOf X) := h.admits.trans (Thm211.normalizer_le_normalizer_kOf X)
    have hAX' : Admits A (kOf X ⊔ iThetaU A X Y) :=
      hAK.sup (le_sup_right.trans (admits_iThetaU (A := A) (X := X) (Y := Y)))
    have hnear' : NearAsolvAction p A (kOf X ⊔ iThetaU A X Y) :=
      Thm211.nearAsolvAction_of_le h hX'X hAX'
    have hcard : Nat.card ↥(kOf X ⊔ iThetaU A X Y) < Nat.card ↥X :=
      Thm211.card_lt_of_ne hX'X hX'
    have hP' : (X₁, X₂) ∈ iPairsY A (kOf X ⊔ iThetaU A X Y) Y := by
      rw [iPairsY_of_le hDX' hX'X]
      exact ⟨hP, (pair_le_iThetaU hP).trans le_sup_right⟩
    exact (concl_iff_of_le hP hX'X le_sup_right le_sup_left).mp
      (ih Γ A (kOf X ⊔ iThetaU A X Y) Y hcard hnear' ⟨_, hP'⟩)

theorem thm33b_below
    (p : ℕ) (n : ℕ) : Thm33bBelow.{u} p n := by
  induction n with
  | zero =>
    intro Γ _ _ A X Y hn
    exact absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro Γ _ _ A X Y hn h hY
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hlt | heq
    · exact ih Γ A X Y hlt h hY
    · exact concl_step (heq ▸ ih) h hY

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b

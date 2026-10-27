module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aUDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

@[expose] def FunTwoType : StatedLieTag → ℕ → Prop
  | .PSL, n => n = 4 ∨ n = 5
  | .PSU, n => n = 4 ∨ n = 5
  | .PSp, n => n = 2
  | .POmegaOdd, n => n = 3
  | .POmegaMinus, n => n = 4
  | .G2, _ => True
  | .trialityD4, _ => True
  | _, _ => False

@[expose] def FunManyType : StatedLieTag → ℕ → Prop
  | .PSL, n => 6 ≤ n
  | .PSU, n => 6 ≤ n
  | .PSp, n => 3 ≤ n
  | .POmegaOdd, n => 4 ≤ n
  | .POmegaPlus, n => 4 ≤ n
  | .POmegaMinus, n => 5 ≤ n
  | .F4, _ => True
  | .E6, _ => True
  | .E7, _ => True
  | .E8, _ => True
  | .twistedE6, _ => True
  | _, _ => False

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR34L3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ f : ℕ,
    (LieModel (BarInf L) .PSL 3 p f ∨ LieModel (BarInf L) .PSU 3 p f) →
    (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

@[expose] def S21_12aFR34F2 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f → FunTwoType t n →
    LieModel (BarInf L) t n p f → (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

@[expose] def S21_12aFR34F3 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n p f → FunManyType t n →
    LieModel (BarInf L) t n p f → (∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f) →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → F08.Thin8 L

theorem s21_12aFR34_of_cases {D : Data G} {Ch : Choice2011 G}
    (hree : ∀ (_ : H1930 D) (_ : Ctx21 D Ch), ∀ L ∈ calC D.M, ∀ f : ℕ,
      LieModel (BarInf L) .twistedG2 0 3 f → False)
    (hL3 : S21_12aFR34L3 D Ch) (hF2 : S21_12aFR34F2 D Ch) (hF3 : S21_12aFR34F3 D Ch) :
    S21_12aFR34 D Ch := by
  rintro hH c L hL p hp hp2 ⟨t, n, f, hadm, hm⟩ hno hfaith
  have h2 : FunTwoType t n → F08.Thin8 L := fun ht =>
    hF2 hH c L hL p hp hp2 t n f hadm ht hm hno hfaith
  have h3 : FunManyType t n → F08.Thin8 L := fun ht =>
    hF3 hH c L hL p hp hp2 t n f hadm ht hm hno hfaith
  obtain ⟨-, -, ht⟩ := hadm
  cases t with
  | PSL =>
    obtain ⟨hn, -, -⟩ := ht
    rcases (by omega : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n) with rfl | rfl | h | h | h
    · exact (hno f hm).elim
    · exact hL3 hH c L hL p hp hp2 f (Or.inl hm) hno hfaith
    · exact h2 (Or.inl h)
    · exact h2 (Or.inr h)
    · exact h3 h
  | PSU =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 3 ∨ n = 4 ∨ n = 5 ∨ 6 ≤ n) with rfl | h | h | h
    · exact hL3 hH c L hL p hp hp2 f (Or.inr hm) hno hfaith
    · exact h2 (Or.inl h)
    · exact h2 (Or.inr h)
    · exact h3 h
  | PSp =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 2 ∨ 3 ≤ n) with h | h
    · exact h2 h
    · exact h3 h
  | POmegaOdd =>
    obtain ⟨hn, -⟩ := ht
    rcases (by omega : n = 3 ∨ 4 ≤ n) with h | h
    · exact h2 h
    · exact h3 h
  | POmegaPlus => exact h3 ht
  | POmegaMinus =>
    have hn : 4 ≤ n := ht
    rcases (by omega : n = 4 ∨ 5 ≤ n) with h | h
    · exact h2 h
    · exact h3 h
  | G2 => exact h2 trivial
  | trialityD4 => exact h2 trivial
  | F4 => exact h3 trivial
  | E6 => exact h3 trivial
  | E7 => exact h3 trivial
  | E8 => exact h3 trivial
  | twistedE6 => exact h3 trivial
  | twistedG2 =>
    obtain ⟨rfl, rfl, -, -⟩ := ht
    exact (hree hH c L hL f hm).elim
  | twistedB2 => exact absurd ht.2.1 hp2
  | twistedF4 => exact absurd ht.2.1 hp2
  | Tits => exact absurd ht.2.1 hp2

end CFSG.LocalAnalysis.UniquenessCase.UC22

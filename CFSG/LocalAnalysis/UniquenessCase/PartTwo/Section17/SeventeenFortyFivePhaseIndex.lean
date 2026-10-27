module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open scoped Pointwise commutatorElement

theorem phase45_index_cases (d : TauCeti.ValidLieTypeIndex) (h2 : d.1.characteristic ≠ 2) :
    (∃ m, d.1 = .reeG2 m) ∨ SmallWeylIndex45 d.1 ∨ BigNonLinIndex45 d.1 ∨
      ∃ (r : ℕ) (q : TauCeti.PrimePower), 4 ≤ r ∧ (d.1 = .A r q ∨ d.1 = .twistedA r q) := by
  revert h2
  rcases d with ⟨d, -⟩
  cases d with
  | A r q =>
    intro _
    by_cases h : r ≤ 3
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ⟨r, q, by omega, Or.inl rfl⟩))
  | twistedA r q =>
    intro _
    by_cases h : r ≤ 3
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr ⟨r, q, by omega, Or.inr rfl⟩))
  | B r q =>
    intro _
    by_cases h : r ≤ 4
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by omega : 5 ≤ r)))
  | C r q =>
    intro _
    by_cases h : r ≤ 4
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by omega : 5 ≤ r)))
  | D r q =>
    intro _
    by_cases h : r ≤ 4
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by omega : 5 ≤ r)))
  | twistedD r q =>
    intro _
    by_cases h : r ≤ 4
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by omega : 5 ≤ r)))
  | E6 q => intro _; exact Or.inr (Or.inr (Or.inl trivial))
  | E7 q => intro _; exact Or.inr (Or.inr (Or.inl trivial))
  | E8 q => intro _; exact Or.inr (Or.inr (Or.inl trivial))
  | F4 q => intro _; exact Or.inr (Or.inl trivial)
  | G2 q => intro _; exact Or.inr (Or.inl trivial)
  | twistedE6 q => intro _; exact Or.inr (Or.inr (Or.inl trivial))
  | trialityD4 q => intro _; exact Or.inr (Or.inl trivial)
  | suzuki m =>
    intro h2
    exact absurd (TauCeti.LieTypeIndex.characteristic_suzuki m) h2
  | reeG2 m => intro _; exact Or.inl ⟨m, rfl⟩
  | reeF4 m =>
    intro h2
    exact absurd (TauCeti.LieTypeIndex.characteristic_reeF4 m) h2
  | tits =>
    intro h2
    exact absurd TauCeti.LieTypeIndex.characteristic_tits h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847G4
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847Fields
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.E9O2Normal
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847Thin17 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, F08.Thin8 Y → ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 →
    Nat.card X = q → ∀ p ∈ D.sig,
      normalizer (X : Set G) ≤ D.M ∨ (p = 3 ∧ E9O2Normal D.M)

theorem r847Thin17_of_r847G4 {D : Data G} (h : R847G4 D) : R847Thin17 D := by
  intro Y hY hthin X hXY q hq hq2 hXq p hp
  rcases h Y hY X hXY q hq hq2 hXq p hp (Or.inl hthin) with
    h1 | ⟨n, hSU3, hn6, -⟩ | ⟨ℓ, f, -, hp3, -, -, A, hA, hLA, ⟨hiso⟩⟩
  · exact Or.inl h1
  · exfalso
    have hodd : Odd n := by
      rw [Nat.odd_iff]
      omega
    have h3r : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 Y)) :=
      two_le_pRank_three_of_isSU3 hSU3 hodd
    rw [pRank_bar2_eq_of_odd (Y := Y) Nat.prime_three (by norm_num)] at h3r
    have := hthin 3 Nat.prime_three (by norm_num)
    omega
  · letI := hA
    exact Or.inr ⟨hp3, e9O2Normal_of_mulEquiv hLA hiso⟩

@[expose] def R847Sec17 (D : Data G) : Prop := R847Thin17 D ∧ R847SU3G4 D

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

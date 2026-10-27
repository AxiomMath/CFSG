module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem exists_scalar_ne_zero_one (hq : 4 ≤ Nat.card K) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set K) ⊆ {0, 1} := fun c _ => by
    by_cases h0 : c = 0
    · simp [h0]
    · simp [h c h0]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({0, 1} : Set K).ncard ≤ 2 := by
    refine (Set.ncard_insert_le 0 {1}).trans ?_
    simp
  rw [Set.ncard_univ] at h1
  omega

end CFSG.RankThree.GF2n.Stroth80.Classify

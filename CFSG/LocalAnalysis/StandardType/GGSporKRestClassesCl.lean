module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRest_generating_of_pgroup_closure {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (a b : K) (hab : Subgroup.closure ({a, b} : Set K) = ⊤)
    (S₀ : Subgroup K) (hS₀ : IsPGroup p S₀) (x₀ : K) (Z : Set K)
    (hZ : ∀ z ∈ Z, ∃ h y : K, y ∈ S₀ ∧ h⁻¹ * x₀ * h = y ∧ z * y = y * z)
    (ha : a ∈ Subgroup.closure ((S₀ : Set K) ∪ Z))
    (hb : b ∈ Subgroup.closure ((S₀ : Set K) ∪ Z)) {x : K} (hx : IsConj x₀ x) :
    SporKRestGenerating p x := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSS⟩ := hS₀.exists_le_sylow
  refine ggSporKRest_generating_of_closure hp S hx Z ?_ ?_
  · intro z hz
    obtain ⟨h, y, hy, hxy, hzy⟩ := hZ z hz
    exact ⟨h, y, hSS hy, hxy, Subgroup.mem_centralizer_singleton_iff.mpr hzy⟩
  · have hle : Subgroup.closure ((S₀ : Set K) ∪ Z) ≤ Subgroup.closure ((S : Set K) ∪ Z) :=
      Subgroup.closure_mono (Set.union_subset_union_left Z hSS)
    rw [eq_top_iff, ← hab, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hle ha
    · exact hle hb

end CFSG.StandardType.SporadicShape

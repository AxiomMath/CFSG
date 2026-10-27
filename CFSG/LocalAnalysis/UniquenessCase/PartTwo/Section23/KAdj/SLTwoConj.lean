module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsSLn)
open scoped MatrixGroups

theorem kAdjData_of_conj {K : Type} [Field K] {G : Type} [Group G] (f : SL(2, K) →* G)
    (hf : Function.Injective f) {n r : ℕ} (hSL : IsSLn ↥f.range 2 n) (T : G)
    (D : SL(2, K)) (hD : orderOf D = r) (hconj : ∀ A, T * f A * T⁻¹ = f (D * A * D⁻¹)) :
    IsSLn ↥f.range 2 n ∧ T ∈ Subgroup.normalizer (f.range : Set G) ∧
      ∃ d ∈ f.range, orderOf d = r ∧ ∀ x ∈ f.range, T * x * T⁻¹ = d * x * d⁻¹ := by
  refine ⟨hSL, ?_, f D, MonoidHom.mem_range.mpr ⟨D, rfl⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [hconj A]
      exact MonoidHom.mem_range.mpr ⟨D * A * D⁻¹, rfl⟩
    · intro hx
      obtain ⟨A', hA'⟩ := MonoidHom.mem_range.mp hx
      refine MonoidHom.mem_range.mpr ⟨D⁻¹ * A' * D, ?_⟩
      have h1 : T * f (D⁻¹ * A' * D) * T⁻¹ = f A' := by
        rw [hconj (D⁻¹ * A' * D)]
        group
      have h2 : T * f (D⁻¹ * A' * D) * T⁻¹ = T * x * T⁻¹ := by rw [h1, hA']
      exact mul_left_cancel (mul_right_cancel h2)
  · rw [orderOf_injective f hf D, hD]
  · intro x hx
    obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [hconj A]
    simp only [map_mul, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

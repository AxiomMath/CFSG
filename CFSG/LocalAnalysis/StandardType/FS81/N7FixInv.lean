module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixInvLow
public import CFSG.LocalAnalysis.StandardType.FS81.N7FixInvComb

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem E6set_subset_evenFix0 : E6set ⊆ evenFix0 7 := by
  rintro _ ⟨S, h0, hS, rfl⟩
  exact q2nN7_sgn_mem_evenFix0 h0 (by rw [hS]; decide)

theorem mem_E6set_of_fixCount {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ evenFix0 7)
    (h2 : M * M = 1) (h9 : fixCount M = 9) : M ∈ E6set := by
  obtain ⟨σ, s, hs, ⟨hσ0, hs0, hprod⟩, rfl⟩ := hM
  have hsq := q2nN7_sq_of_mul_self hs h2
  have hone : ∀ i i' : Fin 8, i ≠ 0 → i' ≠ 0 → (σ i ≠ i ∨ s i = 1) → (σ i' ≠ i' ∨ s i' = 1) →
      i' = i ∨ i' = σ i := by
    intro i i' hi hi' hgi hgi'
    by_contra hcon
    have h27 := q2nN7_fixCount_ge_27 hσ0 hs0 hsq hi hi' hgi hgi'
      (fun h => hcon (Or.inl h)) (fun h => hcon (Or.inr h))
    omega
  exact q2nN7_classify hs hσ0 hs0 hprod hsq hone

end CFSG.StandardType.FrameRoute.FS81

end

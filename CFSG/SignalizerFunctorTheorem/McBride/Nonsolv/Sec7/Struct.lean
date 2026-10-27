module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Basic

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem isRegFam_lcal
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥)
    (hK : kOf (thetaOf θ B) = thetaOf θ B) :
    IsRegFam A (thetaOf θ B) (lcal (thetaOf θ B)) (bN A θ B) := by
  refine ⟨?_, h.lcal_thetaOf_nonempty hBA hB, ?_, ?_, ?_, ?_⟩
  · have := isDirectProduct_lcal_kOf (h.sol_thetaOf hBA hB)
    rwa [hK] at this
  · intro L hL hbot
    obtain ⟨-, -, -, hnc⟩ := mem_lcal_iff.mp hL
    subst hbot
    exact hnc inferInstance
  · intro a ha L hL
    exact map_conj_mem_lcal hL (h.isFunctor.normalizes_thetaOf hBA ha)
  · intro L hL L' hL'
    exact h.exists_conj_eq_of_mem_lcal hBA hB hL hL'
  · intro L hL
    exact (h.bN_eq_inf_normalizer hBA hB hL).symm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

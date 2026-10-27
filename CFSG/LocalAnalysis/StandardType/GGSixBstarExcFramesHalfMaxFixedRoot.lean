module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMinkowski
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxMod
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxRank
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxLattice
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxNormTwo
public import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6

open scoped Matrix

section FixedRoot


theorem halfMaxFixedRoot_E7_E8 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : HalfMaxFixedRoot τ p := by
  intro w hge hlt
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h1 : modMat p (weylMatrix (w * w)) = 1 :=
    modMat_weylMatrix_mul_self_eq_one hτ hp hp2 w hge
  have hww : w * w = 1 := eq_one_of_modMat_weylMatrix_eq_one hτ hp3 h1
  have hM : weylMatrix w * weylMatrix w = 1 := by
    rw [← weylMatrix_mul, hww, weylMatrix_one]
  obtain ⟨u, c, hu, hc, hprim, hMx⟩ :=
    exists_primitive_rank_one_of_involution hp hp2 (weylMatrix w) hM hge hlt
  have hiso : ∀ x y, iform (weylMatrix w *ᵥ x) (weylMatrix w *ᵥ y) = iform x y := by
    intro x y
    rw [weylMatrix_mulVec, weylMatrix_mulVec]
    exact iform_smul w x y
  have hkey := iform_mul_dotProduct_eq_two_mul (weylMatrix w) hiso hu hc hMx
  have hdvd : ∀ x, iform u u ∣ 2 * iform u x := fun x => ⟨c ⬝ᵥ x, (hkey x).symm⟩
  have hnorm : iform u u = 2 := iform_self_eq_two_of_primitive_dvd hτ hu hprim hdvd
  have hroot : IsRoot τ u := isRoot_of_iform_self_eq_two hτ hnorm
  have hcu : c ⬝ᵥ u = 2 := by
    have := hkey u
    rw [hnorm] at this
    omega
  refine ⟨u, hroot, ?_⟩
  rw [← weylMatrix_mulVec, hMx u, hcu]
  ext j
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

end FixedRoot

end ExcFramesHalf

end CFSG.StandardType

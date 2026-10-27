module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.ComponentClassification.CatalogueBHigherLinearField
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts

theorem exists_lift_aut_psl_linear {p f : ℕ} {K : Type} [Field K] (hK : PiField true p f K)
    (ζ : MulAut (projImage (slPi true 3 (p ^ f) K))) (hζ : ζ ^ 3 = 1) :
    ∃ ζ' : MulAut (slPi true 3 (p ^ f) K), ζ' ^ 3 = 1 ∧
      ∀ s, projOf (slPi true 3 (p ^ f) K) (ζ' s) = ζ (projOf (slPi true 3 (p ^ f) K) s) := by
  haveI := hK.finite
  set ψ := pslEquivProjective (p ^ f) K with hψ
  set α := MulAut.congr ψ ζ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hζ, map_one]
  have key : ∃ γ : MulAut (Matrix.SpecialLinearGroup (Fin 3) K), descendAut 3 K γ = α := by
    by_cases hD : α ∈ linearAutGroup 3 K
    · obtain ⟨A, hA⟩ := (mem_linearAutGroup_iff (n := 3) (K := K)).mp hD
      exact ⟨slConjugation 3 K A, hA⟩
    · obtain ⟨σ, -, H, hαH⟩ := linear_order_three_field_descent le_rfl α hα3 hD
      refine ⟨slConjugation 3 K H * slFieldAut (Fin 3) K σ * (slConjugation 3 K H)⁻¹, ?_⟩
      rw [hαH, map_mul, map_mul, map_inv]
      rfl
  obtain ⟨γ, hγ⟩ := key
  have hγ3 : γ ^ 3 = 1 := eq_of_descendAut_eq (by rw [map_pow, hγ, hα3, map_one])
  have hproj : ∀ t : Matrix.SpecialLinearGroup (Fin 3) K,
      ψ.symm (proj 3 K t) = slToPsl (p ^ f) K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, pslEquivProjective_slToPsl]
  have hcoe : ∀ t : Matrix.SpecialLinearGroup (Fin 3) K,
      ζ (slToPsl (p ^ f) K t) = ψ.symm (α (proj 3 K t)) := by
    intro t
    rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, ← pslEquivProjective_slToPsl (q := p ^ f),
      MulEquiv.symm_apply_apply]
  refine ⟨MulAut.congr (slPiTrueEquiv (p ^ f) K).symm γ, ?_, fun s => ?_⟩
  · rw [← map_pow, hγ3, map_one]
  · have hs : projOf (slPi true 3 (p ^ f) K) s =
        slToPsl (p ^ f) K (slPiTrueEquiv (p ^ f) K s) := by
      change projOf _ s = projOf _ ((slPiTrueEquiv (p ^ f) K).symm (slPiTrueEquiv (p ^ f) K s))
      rw [MulEquiv.symm_apply_apply]
    rw [hs, hcoe, ← hγ, descendAut_proj, hproj, MulAut.congr_apply, MulEquiv.symm_symm]
    rfl

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end

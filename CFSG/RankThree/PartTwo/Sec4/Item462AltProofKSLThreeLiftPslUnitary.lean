module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts

theorem exists_lift_aut_psl_unitary {p f : ℕ} {K : Type} [Field K] (hK : PiField false p f K)
    (hq2 : 2 < p ^ f) (ζ : MulAut (projImage (slPi false 3 (p ^ f) K))) (hζ : ζ ^ 3 = 1) :
    ∃ ζ' : MulAut (slPi false 3 (p ^ f) K), ζ' ^ 3 = 1 ∧
      ∀ s, projOf (slPi false 3 (p ^ f) K) (ζ' s) = ζ (projOf (slPi false 3 (p ^ f) K) s) := by
  have h := hK.unitary
  haveI := hK.finite
  set ψ := psuEquivUnitary h with hψ
  set α := MulAut.congr ψ ζ with hα
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, hζ, map_one]
  have key : ∃ γ : MulAut (unitarySU p f K 3),
      MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ) = α := by
    by_cases hD : α ∈ (psuConj h).range
    · obtain ⟨A, hA⟩ := hD
      exact ⟨suConj h A, by rw [congr_centerDescend_suConj, hA]⟩
    · obtain ⟨σ, -, H, hαH⟩ := unitary_order_three_field_descent hq2 α hα3 hD
      refine ⟨suConj h H * suField h σ * (suConj h H)⁻¹, ?_⟩
      rw [hαH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, congr_centerDescend_suConj,
        congr_centerDescend_suField]
  obtain ⟨γ, hγ⟩ := key
  have hγ3 : γ ^ 3 = 1 := eq_of_centerDescend_eq h hq2
    (by rw [map_pow, map_pow, hγ, hα3, map_one, map_one])
  have hproj : ∀ t : unitarySU p f K 3, ψ.symm (unitaryProj h 3 t) = suToPsu p f K t := by
    intro t
    rw [MulEquiv.symm_apply_eq, psuEquivUnitary_suToPsu]
  have hcoe : ∀ t : unitarySU p f K 3,
      ζ (suToPsu p f K t) = ψ.symm (α (unitaryProj h 3 t)) := by
    intro t
    rw [hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, ← psuEquivUnitary_suToPsu h, MulEquiv.symm_apply_apply]
  have hdesc : ∀ t : unitarySU p f K 3,
      (MulAut.congr (suCenterEquiv h hq2) (centerDescend _ γ)) (unitaryProj h 3 t) =
        unitaryProj h 3 (γ t) := fun t => rfl
  refine ⟨MulAut.congr (slPiFalseEquiv p f K).symm γ, ?_, fun s => ?_⟩
  · rw [← map_pow, hγ3, map_one]
  · have hs : projOf (slPi false 3 (p ^ f) K) s = suToPsu p f K (slPiFalseEquiv p f K s) := rfl
    rw [hs, hcoe, ← hγ, hdesc, hproj]
    rfl

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end

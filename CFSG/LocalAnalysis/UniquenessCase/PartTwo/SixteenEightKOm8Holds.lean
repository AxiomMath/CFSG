module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOm8Stab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKOm8S3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.StandardType CFSG.StandardType.Triality CFSG.StandardType.D4Rank
open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem s16kOmega8OutInner_holds : S16kOmega8OutInner := by
  intro K _ _ hK α θ hα hαθ hθ
  haveI : CharP K 2 := CFSG.EvenSmallLie.OmegaEight.charP_two_of_card_eq_two hK
  let e := statedDerivedPlusEquiv K 4
  have hα' : MulAut.congr e α ∈ om8Stab K := by
    have h := (s16kTwistIso_iff_om8 1 α).1 hα
    rwa [map_one] at h
  have hαθ' : MulAut.congr e θ * MulAut.congr e α * (MulAut.congr e θ)⁻¹ ∈ om8Stab K := by
    have h := (s16kTwistIso_iff_om8 1 (θ * α * θ⁻¹)).1 hαθ
    rwa [map_one, map_mul, map_mul, map_inv] at h
  have hθ' : MulAut.congr e θ ∉ om8Stab K := fun h =>
    hθ ((s16kTwistIso_iff_om8 1 θ).2 (by rwa [map_one]))
  have hin := s16kOm8_inner_of_stab (om8_card_mulAut hK) (om8_center_eq_bot hK) (om8Stab K)
    (inner_le_om8Stab K) (plusRefl_mem_om8Stab K) (AutOm.plusRefl_mul_self one_le_four)
    (theta_not_mem_om8Stab K) theta_cube plusRefl_theta_plusRefl hα' hθ' hαθ'
  obtain ⟨h, hh⟩ := hin
  refine ⟨e.symm h, fun x => ?_⟩
  have h1 := congrArg (fun β : MulAut (Om8 K) => e.symm (β (e x))) hh
  simpa [MulAut.conj_apply] using h1.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

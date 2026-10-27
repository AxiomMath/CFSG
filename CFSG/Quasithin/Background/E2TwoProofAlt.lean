module

public import CFSG.Quasithin.Background.E2TwoProofAS
public import CFSG.Quasithin.Background.E2TwoProofBender
public import CFSG.Quasithin.Background.E2TwoProofA6
public import CFSG.Quasithin.Background.E2TwoProofA7
public import CFSG.Quasithin.Background.E2TwoProofA8
public import CFSG.Quasithin.Background.E2TwoProofL52
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace E2P

theorem e22AltFam :
    E22AltFam := by
  intro X _ _ K T M hX
  refine ⟨fun h5 => ?_, fun h6 => ?_, fun ⟨e⟩ => hX.not_a7 e, fun ⟨e⟩ => hX.not_a8 e⟩
  · have hA5 : IsAlt 5 ↥K := h5.elim id Setup.Family.alternating_five_of_model_five
    have hL : IsPSL 2 2 2 ↥K := Ch1.statedClassicalModel_psl_two_four_of_alternating_five _ hA5
    exact ⟨hL, hX.isBorelIn_of_bender (A5.C25.fusionIsBenderGroup_of_isPSL hL)⟩
  · have hA6 : IsAlt 6 ↥K := h6.elim id Setup.Family.alternating_six_of_model_nine
    obtain ⟨e⟩ := hA6
    exact ⟨isSp4Prime_one_iff.mpr ⟨e⟩, hX.a6 e⟩

theorem e22LnTwoFam : E22LnTwoFam := by
  intro X _ _ K T M hX n hn h
  rcases hn with rfl | rfl
  · obtain ⟨e⟩ := (ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff ↥K).mp
      (Or.inl ⟨by decide, h⟩)
    exact hX.not_a8 e
  · exact hX.not_l52 h

end E2P

end CFSG.Quasithin

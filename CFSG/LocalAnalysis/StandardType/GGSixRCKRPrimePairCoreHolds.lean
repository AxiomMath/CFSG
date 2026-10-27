module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCoreUntw
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimePairCoreTw

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
  CFSG.StandardType.GGFinModel


theorem rckFramePairCore_holds : RCKFramePairCore :=
  rckFramePairCore_of_good fun τ hτ S => by
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · refine rckPairCoreGood_untw hτ S ⟨Fr, hFr, ?_⟩
      ext1 g
      rw [hΦ, one_mul, inv_one, mul_one]
    · subst ht
      refine rckPairCoreGood_tw t S ⟨Fr, hFr, ?_⟩
      ext1 g
      rw [hΦ]
      simp [twistHom, diagramAt, MulAut.conj_apply]

end CFSG.StandardType.RCKRP

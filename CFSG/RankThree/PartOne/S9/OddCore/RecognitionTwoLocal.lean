module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.RankThreeEven
open CFSG.RankThree.PartOne.OddCore37
open scoped commutatorElement

theorem twoLocalRankTwoOddCoreAction_of
    (hCO2AR : CriticalOddCoreTwoActionRecognition)
    (hE2AOCTL : ExtraspecialTwoActionOddCoreTorsionLifting) :
    TwoLocalRankTwoOddCoreAction := by
  intro G _ _ p q A R hp hq hp3 hq3 hpq hA hAR hR2 hRne hRA hRQ hloc
  have hQn : (pCore q G).Normal := pCore_normal
  have hQp : IsPGroup q (pCore q G) := pCore_isPGroup
  have hrank : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(pCore q G ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2 := by
    intro r hr hr1
    have hr2 : IsPGroup 2 (Subgroup.zpowers r) := hR2.to_le (Subgroup.zpowers_le.2 hr)
    exact (pRank_inf_centralizer_le_localRank hq (pCore q G) hr1 hr2).trans hloc
  obtain ⟨hp5, hRqd, -, D, hDQ, hDchar, -, -, -, hDR, hRD, -, hDshape⟩ :=
    hCO2AR G p q A R (pCore q G) hp hq hp3 (by omega) hpq hA hR2 hAR hRA hRne hQn hQp hRQ hrank
  have hDn : D.Normal := normal_of_characteristic hDQ hDchar
  have hRnorm : R ≤ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer_of_normal
  have hlift := hE2AOCTL G q A R (pCore q G) D hq (by omega) (by omega) (hp5 ▸ hA) hAR hRA hRqd
    hQn hQp hDQ hDchar hRnorm hRD hDshape hrank
  exact ⟨hp5, hRqd, hlift ▸ hDshape⟩

end CFSG.RankThree.PartOne

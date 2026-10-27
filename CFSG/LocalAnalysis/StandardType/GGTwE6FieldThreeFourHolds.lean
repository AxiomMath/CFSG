module

public import CFSG.LocalAnalysis.StandardType.GGTwE6FieldThreeFour
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.TwE6RootKill


theorem subfieldLangDatumThreeFour_holds : SubfieldLangDatumThreeFour :=
  subfieldLangDatumThreeFour_of_toral ExcFramesHalf.bigElemAbelianToralBar_E6_three

theorem exists_twLangData_of_twNormTwo' {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAI : A ≤ twistedE6InndiagGL K σ) (hA : IsElemAbelian 3 A) (hcard : 3 ^ 4 ≤ Nat.card A)
    (hU : TwNormTwo K σ A) : ∃ D : TwLangData K σ (2 ^ n) A, D.c = 1 :=
  exists_twLangData_of_twNormTwo ExcFramesHalf.bigElemAbelianToralBar_E6_three hK hσ h3 hAI hA
    hcard hU

end CFSG.StandardType.TwE6FieldCore

end

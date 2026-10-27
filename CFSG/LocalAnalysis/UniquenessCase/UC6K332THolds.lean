module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332T3
public import CFSG.LocalAnalysis.UniquenessCase.UC6KMult3Holds
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Alt
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.LieAll
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureThree.Spor
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionFinal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.LocalAnalysis.RankThreeTheoremC

section


theorem kMult3Ab_holds
    : KMult3Ab := by
  intro J _ _ hq hK hZ hrk T hT hΩ
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card (Subgroup.center J) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hZ
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hne
      rw [pow_zero, Subgroup.card_eq_one] at hk
      exact hk
    rw [hk]
    exact dvd_pow_self 3 hk0
  obtain ⟨-, hTp, hTi⟩ := (CFSG.ABGLocalTools.isSylowOf_iff (p := 3)).1 hT
  rw [Subgroup.relIndex_top_right] at hTi
  have h := CFSG.LocalAnalysis.RankThreeTheoremC.kFactCentralOmega_holds J hq
    (catalog_of_quasisimple_uc6 hq hK) hdvd (by omega) (hTp.toSylow hTi)
  apply h
  intro a ha b hb ha3 hb3
  rw [IsPGroup.toSylow_coe] at ha hb
  exact hΩ a ha ha3 b hb hb3

theorem k332ThreeAb_holds
    : K332ThreeAb :=
  k332ThreeAb_of_inputs kMult3Ab_holds
    (WeakClosureThree.dichThree_of_cases WeakClosureThree.dichThreeAlt_holds
      WeakClosureThree.dichThreeLie_holds WeakClosureThree.dichThreeSpor_holds)
    KFactProofs.Stroth.InnerAction.kFactInnerAction_holds
    KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds

theorem k332Three_holds
    : K332Three := k332Three_of_ab k332ThreeAb_holds

end

end CFSG.LocalAnalysis.UniquenessCase.UCK

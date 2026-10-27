module

public import CFSG.LocalAnalysis.UniquenessCase.UC6N588E1
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.CentralOmega.Main

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

theorem catalog_of_quasisimple_uc6 {J : Type} [Group J] [Finite J] (hq : CFSG.Open.IsQuasisimple J)
    (hK : CFSG.Open.IsKGroup (J ⧸ Subgroup.center J)) :
    CFSG.Open.IsCatalogGroup (J ⧸ Subgroup.center J) := by
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hq.2
  exact hK.isCatalogGroup_of_surjective ⊤
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian J hq)
    (Subgroup.topEquiv (G := J ⧸ Subgroup.center J)).toMonoidHom
    (Subgroup.topEquiv (G := J ⧸ Subgroup.center J)).surjective

section


theorem kMult3_holds : KMult3 := by
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
  intro a ha b hb ha3 _
  rw [IsPGroup.toSylow_coe] at ha hb
  exact hΩ a ha ha3 b hb

end

end CFSG.LocalAnalysis.UniquenessCase.UCK

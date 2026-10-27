module

public import CFSG.LocalAnalysis.StandardType.FF81.CatQ1.JFacts
import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.StandardType.FF81.CatQ1

open CFSG.Open

theorem false_of_one_of_product {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) (O J : Subgroup K)
    (hfix : ∀ x : K, x ∈ O ⊔ J ↔ (1 : MulAut K) x = x)
    (hcomm : ∀ x ∈ O, ∀ y ∈ J, x * y = y * x)
    (hJ : StatedClassicalModel J .PSL 4 2 1 ∨ StatedClassicalModel J .PSL 5 2 1) : False := by
  have htop : O ⊔ J = ⊤ := by
    ext x
    rw [hfix x]
    simp
  have hJnormal : J.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply eq_top_iff.mpr
    rw [← htop]
    apply sup_le
    · rw [Subgroup.le_normalizer_iff]
      intro o ho k hk
      have hconj : o * k * o⁻¹ = k := by rw [hcomm o ho k hk]; group
      rwa [hconj]
    · exact Subgroup.le_normalizer
  rcases Subgroup.Normal.eq_bot_or_eq_top J with hbot | hJtop
  · have hdvd : 20160 ∣ Nat.card ↥J := twentyThousand_dvd_card_of_modelJ ↥J hJ
    rw [hbot, Subgroup.card_bot] at hdvd
    norm_num at hdvd
  ·
    have e : ↥J ≃* K := (MulEquiv.subgroupCongr hJtop).trans Subgroup.topEquiv
    have hp : 1 < 3 := by norm_num
    have heq := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (G := ↥J) (G' := K) hp e
    have hle : CFSG.Open.pRank 3 (⊤ : Subgroup ↥J) ≤ 2 :=
      pRank_three_le_two_of_modelJ ↥J hJ
    rw [← heq] at h4
    omega

end CFSG.StandardType.FF81.CatQ1

module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
import CFSG.RankThree.GF2n.Parrott.Lemma13ExistsSylow
import CFSG.RankThree.GF2n.Parrott.Lemma13Representative
import CFSG.RankThree.GF2n.Parrott.Lemma13Reduce
import CFSG.RankThree.GF2n.Parrott.Lemma13SylowFacts
public import CFSG.RankThree.GF2n.Parrott.Section2Cases

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem no_conj_z_eq_of_mem_tJ_equalityBranch (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹)
    (hstar : ∀ g : G, CFSG.conjugate (Subgroup.zpowers (σ : G)) g ≤ H z →
      ∃ h' ∈ H z, CFSG.conjugate (Subgroup.zpowers (σ : G)) g =
        CFSG.conjugate (Subgroup.zpowers (σ : G)) h')
    (hNσ : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G),
      ∃ h' ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G) ⊓ H z,
        ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G), h' * c = n) :
    ∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x := by
  obtain ⟨t, ht, htσ⟩ := exists_lift_tH_commute_sigma1Nine_mul_inv D hσ₂ hq₂ hcomm hσ
  have hσ3 : orderOf σ = 3 := by
    rw [hσ]
    exact orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂
      hcomm
  have htJ : (t : G) ∉ J z := by
    intro htJ
    have hq1 : qH D t = 1 := (J_mem_iff D t).mp (Subgroup.mem_subgroupOf.mpr htJ)
    have h1 := (J_mem_iff D _).mp ht
    rw [map_mul, map_inv, qH_tH, hq1, mul_one, inv_eq_one] at h1
    exact t_ne_one (congrArg Subtype.val h1)
  have hmain := no_conj_z_eq_of_mem_tJ_exists_sylow (t := t) (σ := (σ : G))
    (congrArg Subtype.val htσ) htJ σ.2 ((Subgroup.orderOf_coe σ).trans hσ3)
    (reduce_tJ_tCJ_of_equalityBranch D h hσ₂ hq₂ hcomm hEq hσ ht htσ)
    (exists_sylow_of_mem_tCJ_of_equalityBranch D h hσ₂ hq₂ hcomm hEq hJ hσ ht htσ) hstar hNσ
  intro x hx hx2 g hg
  exact hmain x ((cosetJ_tH_iff_of_inv_mul_mem D ht x).mpr hx) hx2 g hg

end CFSG.RankThree.GF2n.Parrott

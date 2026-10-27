module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm13_10.FiveCentralB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SU3MinDegreeHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem false_of_both_normal (hInv : KA5InvertsThree) {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L K : Subgroup (MulAut W)} (hO2 : O2Trivial Y)
    (hB : IsBasicModule Y) (hcL : IsComponentOf L Y) (hcK : IsComponentOf K Y) (hne : L ≠ K)
    (hnL : (L.subgroupOf Y).Normal) (hnK : (K.subgroupOf Y).Normal) {t : MulAut W}
    (htY : t ∈ Y) (ht2 : orderOf t = 2) (htm : rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (haK : IsAlt ↥K 5) (haL : IsAlt ↥L 5 ∨ LieModel ↥L .PSU 3 2 2) : False := by
  have hcomm : ∀ a ∈ L, ∀ b ∈ K, a * b = b * a :=
    B69.components_mul_comm_of_ne hcK hcL hne.symm
  have hVK : commSub (⊤ : Subgroup W) K = ⊤ :=
    commSub_top_eq_top_of_normal hW hO2 hB hcK hnK
  have hVL : commSub (⊤ : Subgroup W) L = ⊤ :=
    commSub_top_eq_top_of_normal hW hO2 hB hcL hnL
  have hnormL : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcL.1).mp hnL
  have hnormK : Y ≤ Subgroup.normalizer (K : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcK.1).mp hnK
  have htL : t ∈ Subgroup.normalizer (L : Set (MulAut W)) := hnormL htY
  have htK : t ∈ Subgroup.normalizer (K : Set (MulAut W)) := hnormK htY
  have hL1 : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp
      (CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow.nontrivial_of_isQuasisimple hcL.2.2)
  have ht2' : t ^ 2 = 1 := by
    rw [← ht2]
    exact pow_orderOf_eq_one t
  have hncK : ∃ x ∈ K, t * x ≠ x * t := by
    by_contra h
    push Not at h
    have htd : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥K := by
      rw [dMinDeg_eq_four_of_isAlt_five haK]
      omega
    have hle := commSub_le_fixV_zpowers_of_commute hW h htd
    rw [hVK] at hle
    have htop : fixV (Subgroup.zpowers t) = ⊤ := top_le_iff.mp hle
    have ht1 : t = 1 := by
      ext w
      exact mem_fixV.mp (by rw [htop]; exact Subgroup.mem_top w) t
        (Subgroup.mem_zpowers t)
    rw [ht1, orderOf_one] at ht2
    norm_num at ht2
  rcases haL with haL | haL
  ·
    have hncL : ∃ x ∈ L, t * x ≠ x * t := by
      by_contra h
      push Not at h
      have htd : rkIdx (fixV (Subgroup.zpowers t)) < dMinDeg ↥L := by
        rw [dMinDeg_eq_four_of_isAlt_five haL]
        omega
      have hle := commSub_le_fixV_zpowers_of_commute hW h htd
      rw [hVL] at hle
      have htop : fixV (Subgroup.zpowers t) = ⊤ := top_le_iff.mp hle
      have ht1 : t = 1 := by
        ext w
        exact mem_fixV.mp (by rw [htop]; exact Subgroup.mem_top w) t
          (Subgroup.mem_zpowers t)
      rw [ht1, orderOf_one] at ht2
      norm_num at ht2
    have hKfix : commSub (⊤ : Subgroup W) K ≤ fixV L :=
      commSub_le_fixV_of_isAlt_five_pair hW haL haK hcomm htL hncL htm
    rw [hVK] at hKfix
    have hfixL : fixV L = ⊤ := top_le_iff.mp hKfix
    exact hL1 (by
      rw [eq_bot_iff]
      intro l hl
      ext w
      exact mem_fixV.mp (by rw [hfixL]; exact Subgroup.mem_top w) l hl)
  ·
    have hU3 : IsU3 ↥L 2 := haL
    have hSU3 : IsSU3 ↥L 2 := (U3Loss.isSU3_of_isU3 hU3).1
    have h12 : 12 ≤ dMinDeg ↥L := by
      simpa using k_SU3MinDegree_holds ↥L 2 hSU3 (by norm_num)
    obtain ⟨z, hzK, hzord, htzi⟩ :=
      hInv (MulAut W) K t haK ht2'
        (fun x hx => (Subgroup.mem_normalizer_iff.mp htK x).mp hx) hncK
    have hz3 : z ^ 3 = 1 := by
      rw [← hzord]
      exact pow_orderOf_eq_one z
    have hE : IsElemAbelian 3 (Subgroup.zpowers z) := isElemAbelian_zpowers hz3
    have hinv : ∀ x ∈ Subgroup.zpowers z, t * x * t⁻¹ = x⁻¹ := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, htzi, inv_zpow']
      rw [zpow_neg]
    have hrk : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers z)) ≤ 6 := by
      have h := SevenFour.rk_commSub_le_two_mul_rkIdx hW Nat.prime_three (by norm_num) hE ht2 hinv
      omega
    have hSL : StableUnder L (commSub (⊤ : Subgroup W) (Subgroup.zpowers z)) := by
      refine stableUnder_commSub ?_ (fun _ _ _ _ => Subgroup.mem_top _)
      intro l hl x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hconj : MulAut.conj l z = z := by
        rw [MulAut.conj_apply, hcomm l hl z hzK]
        group
      have hfix : l * z ^ k * l⁻¹ = z ^ k := by
        rw [← MulAut.conj_apply, map_zpow, hconj]
      rw [hfix]
      exact Subgroup.zpow_mem (Subgroup.zpowers z) (Subgroup.mem_zpowers z) k
    have hbotstab : StableUnder L (⊥ : Subgroup W) := by
      intro x _ u hu
      rw [Subgroup.mem_bot] at hu ⊢
      rw [hu, map_one]
    have hrkS : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers z)) <
        rk ↥(⊥ : Subgroup W) + dMinDeg ↥L := by
      rw [rk_bot]
      omega
    have hkill : commSub (commSub (⊤ : Subgroup W) (Subgroup.zpowers z)) L ≤ ⊥ :=
      commSub_le_of_rk_lt_dMinDeg hW (K := L) (U := ⊥) bot_le hSL hbotstab hrkS
    have hSfix : commSub (⊤ : Subgroup W) (Subgroup.zpowers z) ≤ fixV L :=
      commSub_eq_bot_iff.mp (le_bot_iff.mp hkill)
    have hKstab : K ≤ stabSub (fixV L) := by
      have hKcent : K ≤ Subgroup.centralizer (L : Set (MulAut W)) := by
        intro k' hk'
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact hcomm x hx k' hk'
      have hKnorm : K ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
        hKcent.trans (Subgroup.centralizer_le_normalizer (L : Set (MulAut W)))
      exact hKnorm.trans (le_stabSub_fixV (Y := Subgroup.normalizer (L : Set (MulAut W)))
        (H := L) (fun y hy h hl => (Subgroup.mem_set_normalizer_iff.mp hy h).mp hl))
    have hKsimple : IsSimpleGroup ↥K := by
      obtain ⟨e⟩ := haK
      haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
      exact MulEquiv.isSimpleGroup e
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzord
      norm_num at hzord
    have hKfix : commSub (⊤ : Subgroup W) K ≤ fixV L :=
      commSub_le_of_isSimpleGroup hKsimple hKstab hzK hz1 hSfix
    rw [hVK] at hKfix
    have hfixL : fixV L = ⊤ := top_le_iff.mp hKfix
    exact hL1 (by
      rw [eq_bot_iff]
      intro l hl
      ext w
      exact mem_fixV.mp (by rw [hfixL]; exact Subgroup.mem_top w) l hl)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm13_10

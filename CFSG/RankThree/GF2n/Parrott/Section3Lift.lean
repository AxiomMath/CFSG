module

public import CFSG.RankThree.GF2n.Parrott.FixDimTwo
public import CFSG.RankThree.GF2n.Parrott.OrderNineLiftFixed
public import CFSG.RankThree.GF2n.Parrott.CJConj

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]

noncomputable def nineRoot (D : QuotientData (z := z) hN) : ↥(H z) :=
  (exists_order_nine_root_sigma1 (z := z) D).choose

noncomputable def sigma1Nine (D : QuotientData (z := z) hN) : ↥(H z) :=
  (exists_order_nine_root_sigma1 (z := z) D).choose_spec.choose

theorem nineRoot_order (D : QuotientData (z := z) hN) : orderOf (nineRoot (z := z) D) = 9 :=
  (exists_order_nine_root_sigma1 (z := z) D).choose_spec.choose_spec.1

theorem nineRoot_cube (D : QuotientData (z := z) hN) :
    nineRoot (z := z) D ^ 3 = sigma1Nine (z := z) D :=
  (exists_order_nine_root_sigma1 (z := z) D).choose_spec.choose_spec.2.1

theorem sigma1Nine_order (D : QuotientData (z := z) hN) :
    orderOf (sigma1Nine (z := z) D) = 3 :=
  (exists_order_nine_root_sigma1 (z := z) D).choose_spec.choose_spec.2.2.1

theorem qH_sigma1Nine (D : QuotientData (z := z) hN) :
    qH D (sigma1Nine (z := z) D) = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) :=
  (exists_order_nine_root_sigma1 (z := z) D).choose_spec.choose_spec.2.2.2

theorem conjZ_sigma1Nine (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    conjZ z (sigma1Nine (z := z) D) = 1 := by
  rw [← nineRoot_cube (z := z) D, map_pow, conjZ_cube_eq_one h (nineRoot_order (z := z) D)]

theorem fixDimV_sigma1Nine (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    fixDimV h (sigma1Nine (z := z) D) = 2 :=
  fixDimV_eq_two h (nineRoot_order (z := z) D) (nineRoot_cube (z := z) D)

theorem card_centralizerJ_sigma1Nine (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    Nat.card (centralizerJ (sigma1Nine (z := z) D)) = 16 :=
  card_centralizerJ_eq_sixteen h (nineRoot_order (z := z) D) (nineRoot_cube (z := z) D)

noncomputable def sigma2Nine (D : QuotientData (z := z) hN) : ↥(H z) :=
  uH D * sigma1Nine (z := z) D * (uH D)⁻¹

theorem qH_sigma2Nine (D : QuotientData (z := z) hN) :
    qH D (sigma2Nine (z := z) D) = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) := by
  show qH D (uH D * sigma1Nine (z := z) D * (uH D)⁻¹) = _
  rw [map_mul, map_mul, map_inv, qH_uH, qH_sigma1Nine]
  apply Subtype.ext
  exact sigma1_conj_u

theorem orderOf_sigma2Nine (D : QuotientData (z := z) hN) :
    orderOf (sigma2Nine (z := z) D) = 3 := by
  have hconjord : orderOf (uH D * sigma1Nine (z := z) D * (uH D)⁻¹) =
      orderOf (sigma1Nine (z := z) D) := by
    simpa [MulAut.conj_apply] using
      MulEquiv.orderOf_eq (MulAut.conj (uH D)) (sigma1Nine (z := z) D)
  show orderOf (uH D * sigma1Nine (z := z) D * (uH D)⁻¹) = 3
  rw [hconjord]
  exact sigma1Nine_order (z := z) D

theorem conjZ_sigma2Nine (h : Tim79a.ParrottHyp z) (D : QuotientData (z := z) hN) :
    conjZ z (sigma2Nine (z := z) D) = 1 := by
  show conjZ z (uH D * sigma1Nine (z := z) D * (uH D)⁻¹) = 1
  rw [map_mul, map_mul, map_inv, conjZ_sigma1Nine h D]
  simp

theorem card_centralizerJ_sigma2Nine (h : Tim79a.ParrottHyp z)
    (D : QuotientData (z := z) hN) :
    Nat.card (centralizerJ (sigma2Nine (z := z) D)) = 16 := by
  have hbase : Nat.card ↥(CJ z (sigma1Nine (z := z) D : G)) = 16 := by
    have hh := card_centralizerJ_sigma1Nine h D
    have he : ↥(CJ z (sigma1Nine (z := z) D : G)) ≃
        ↥(centralizerJ (sigma1Nine (z := z) D)) := by
      unfold centralizerJ CJ
      exact ((Subgroup.subgroupOfEquivOfLe (inf_le_right :
        Subgroup.centralizer ({(sigma1Nine (z := z) D : G)} : Set G) ⊓ J z ≤
          J z)).symm).toEquiv
    rw [Nat.card_congr he]
    exact hh
  have hconj := card_CJ_conj (z := z) (uH D) (sigma1Nine (z := z) D)
  have h2 : ((uH D : G) * (sigma1Nine (z := z) D : G) * (uH D : G)⁻¹) =
      (sigma2Nine (z := z) D : G) := rfl
  rw [h2, hbase] at hconj
  have he2 : ↥(CJ z (sigma2Nine (z := z) D : G)) ≃
      ↥(centralizerJ (sigma2Nine (z := z) D)) := by
    unfold centralizerJ CJ
    exact ((Subgroup.subgroupOfEquivOfLe (inf_le_right :
      Subgroup.centralizer ({(sigma2Nine (z := z) D : G)} : Set G) ⊓ J z ≤
        J z)).symm).toEquiv
  rw [← Nat.card_congr he2]
  exact hconj

end CFSG.RankThree.GF2n.Parrott

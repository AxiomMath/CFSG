module

public import CFSG.RankThree.GF2n.Parrott.Setup
public import CFSG.RankThree.GF2n.Parrott.PSp43Model
public import Certificates.Certificate2012

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.GH74.KGroups

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

@[expose] noncomputable def qH : ↥(H z) →* QA45.originalSubgroup :=
  (QuotientData.toQA45 (z := z) (hN := hN) D).toMonoidHom.comp
    (QuotientGroup.mk' ((J z).subgroupOf (H z)))

noncomputable def lift (x : QA45.originalSubgroup) : ↥(H z) :=
  Classical.choose
    (QuotientGroup.mk'_surjective ((J z).subgroupOf (H z))
      ((QuotientData.toQA45 (z := z) (hN := hN) D).symm x))

@[simp] theorem qH_lift (x : QA45.originalSubgroup) : qH D (lift D x) = x := by
  have hspec := Classical.choose_spec
    (QuotientGroup.mk'_surjective ((J z).subgroupOf (H z))
      ((QuotientData.toQA45 (z := z) (hN := hN) D).symm x))
  unfold lift qH
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hspec]
  exact MulEquiv.apply_symm_apply _ _

theorem qH_surjective : Function.Surjective (qH D) := fun x => ⟨lift D x, qH_lift D x⟩

theorem mk_eq_mk_iff (a b : ↥(H z)) :
    QuotientGroup.mk' ((J z).subgroupOf (H z)) a =
        QuotientGroup.mk' ((J z).subgroupOf (H z)) b ↔ qH D a = qH D b := by
  constructor
  · intro h
    have hq : (QuotientData.toQA45 (z := z) (hN := hN) D)
        (QuotientGroup.mk' ((J z).subgroupOf (H z)) a) =
        (QuotientData.toQA45 (z := z) (hN := hN) D)
        (QuotientGroup.mk' ((J z).subgroupOf (H z)) b) := by
      rw [h]
    simpa [qH] using hq
  · intro h
    exact (QuotientData.toQA45 (z := z) (hN := hN) D).injective (by simpa [qH] using h)

theorem mk_eq_of_qH_eq {a b : ↥(H z)} (h : qH D a = qH D b) :
    QuotientGroup.mk' ((J z).subgroupOf (H z)) a =
      QuotientGroup.mk' ((J z).subgroupOf (H z)) b :=
  (mk_eq_mk_iff D a b).mpr h

theorem J_mem_iff (x : ↥(H z)) :
    x ∈ (J z).subgroupOf (H z) ↔ qH D x = 1 := by
  rw [← QuotientGroup.ker_mk' (N := ((J z).subgroupOf (H z))), MonoidHom.mem_ker]
  constructor
  · intro hx
    have hq : (QuotientData.toQA45 (z := z) (hN := hN) D)
        (QuotientGroup.mk' ((J z).subgroupOf (H z)) x) = 1 := by
      rw [hx, map_one]
    simpa [qH] using hq
  · intro hx
    exact (QuotientData.toQA45 (z := z) (hN := hN) D).injective (by simpa [qH] using hx)

noncomputable abbrev tH : ↥(H z) := lift D ⟨t, t_mem_A⟩

noncomputable abbrev uH : ↥(H z) := lift D ⟨u, u_mem_A⟩

noncomputable abbrev vH : ↥(H z) := lift D ⟨v, v_mem_A⟩

noncomputable abbrev s1H : ↥(H z) := lift D ⟨sigma1, sigma1_mem_A⟩

noncomputable abbrev s2H : ↥(H z) := lift D ⟨sigma2, sigma2_mem_A⟩

noncomputable abbrev a1H : ↥(H z) := lift D ⟨alpha1, alpha1_mem_A⟩

noncomputable abbrev b1H : ↥(H z) := lift D ⟨beta1, beta1_mem_A⟩

noncomputable abbrev a2H : ↥(H z) := lift D ⟨alpha2, alpha2_mem_A⟩

noncomputable abbrev b2H : ↥(H z) := lift D ⟨beta2, beta2_mem_A⟩

noncomputable abbrev betaH : ↥(H z) := lift D ⟨beta, beta_mem_A⟩

@[simp] theorem qH_tH : qH D (tH D) = ⟨t, t_mem_A⟩ := qH_lift D _

@[simp] theorem qH_uH : qH D (uH D) = ⟨u, u_mem_A⟩ := qH_lift D _

@[simp] theorem qH_vH : qH D (vH D) = ⟨v, v_mem_A⟩ := qH_lift D _

@[simp] theorem qH_s1H : qH D (s1H D) = ⟨sigma1, sigma1_mem_A⟩ := qH_lift D _

@[simp] theorem qH_s2H : qH D (s2H D) = ⟨sigma2, sigma2_mem_A⟩ := qH_lift D _

@[simp] theorem qH_a1H : qH D (a1H D) = ⟨alpha1, alpha1_mem_A⟩ := qH_lift D _

@[simp] theorem qH_b1H : qH D (b1H D) = ⟨beta1, beta1_mem_A⟩ := qH_lift D _

@[simp] theorem qH_a2H : qH D (a2H D) = ⟨alpha2, alpha2_mem_A⟩ := qH_lift D _

@[simp] theorem qH_b2H : qH D (b2H D) = ⟨beta2, beta2_mem_A⟩ := qH_lift D _

@[simp] theorem qH_betaH : qH D (betaH D) = ⟨beta, beta_mem_A⟩ := qH_lift D _

theorem qH_tH_mem_Q :
    qH D (tH D) ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  rw [qH_tH]
  exact t_mem_Q

theorem qH_vH_not_mem_Q :
    qH D (vH D) ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  rw [qH_vH]
  exact v_not_mem_Q

theorem qH_a2H_mem_Q :
    qH D (a2H D) ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
  rw [qH_a2H]
  exact alpha2_mem_Q

noncomputable def P_H : Subgroup ↥(H z) :=
  Subgroup.comap (qH D) (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup)

theorem mem_P_H_iff (x : ↥(H z)) :
    x ∈ P_H D ↔ qH D x ∈ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
  Iff.rfl

theorem QP45_le_QA45 : QP45.originalSubgroup ≤ QA45.originalSubgroup := by
  rw [QP45_closure, QA45_closure, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem card_QP45 : Nat.card QP45.originalSubgroup = 25920 := by
  rw [card_group QP45 QP45_ok, QP45_valid.2]

theorem card_QA45 : Nat.card QA45.originalSubgroup = 51840 := by
  rw [card_group QA45 QA45_ok, QA45_valid.2]

theorem card_QP45_subgroupOf :
    Nat.card (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) = 25920 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QP45_le_QA45).toEquiv]
  exact card_QP45

theorem index_QP45 :
    (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup).index = 2 := by
  rw [Subgroup.index_eq_card_div, card_QA45, card_QP45_subgroupOf]

theorem J_le_P_H : (J z).subgroupOf (H z) ≤ P_H D := by
  intro x hx
  rw [mem_P_H_iff]
  rw [J_mem_iff D] at hx
  rw [hx]
  exact Subgroup.one_mem _

theorem P_H_normal : (P_H D).Normal :=
  (Subgroup.normal_of_index_eq_two index_QP45).comap (qH D)

theorem index_P_H : (P_H D).index = 2 := by
  unfold P_H
  rw [Subgroup.index_comap_of_surjective
    (H := QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) (f := qH D)
    (qH_surjective D), index_QP45]

theorem uH_mem_P_H : uH D ∈ P_H D := by
  rw [mem_P_H_iff, qH_uH]
  exact u_mem_Q

theorem vH_not_mem_P_H : vH D ∉ P_H D := by
  intro h
  rw [mem_P_H_iff, qH_vH] at h
  exact v_not_mem_Q h

theorem tH_mem_P_H : tH D ∈ P_H D := by
  rw [mem_P_H_iff, qH_tH]
  exact t_mem_Q

theorem a2H_mem_P_H : a2H D ∈ P_H D := by
  rw [mem_P_H_iff, qH_a2H]
  exact alpha2_mem_Q

theorem betaH_mem_P_H : betaH D ∈ P_H D := by
  rw [mem_P_H_iff, qH_betaH]
  exact beta_mem_Q

theorem mk_t_mul_u :
    QuotientGroup.mk' ((J z).subgroupOf (H z)) (tH D * uH D) =
      QuotientGroup.mk' ((J z).subgroupOf (H z)) (uH D * tH D) := by
  rw [mk_eq_mk_iff (D := D)]
  simp only [map_mul, qH_tH, qH_uH]
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, Subgroup.coe_one] using t_commute_u

@[simp] theorem mk_one :
    QuotientGroup.mk' ((J z).subgroupOf (H z)) (1 : ↥(H z)) = 1 := map_one _

end CFSG.RankThree.GF2n.Parrott

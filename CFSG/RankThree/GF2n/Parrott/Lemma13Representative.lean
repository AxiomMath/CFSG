module

public import CFSG.RankThree.GF2n.Parrott.Lemma13
import CFSG.RankThree.GF2n.Parrott.Lemma13Structure
import CFSG.RankThree.GF2n.Parrott.SigmaStarEquality
public import CFSG.RankThree.GF2n.Parrott.Section2Cases
public import CFSG.RankThree.GF2n.Parrott.Section2J0NormalFinal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem exists_lift_tH_commute_sigma1Nine_mul_inv {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹) :
    ∃ t : ↥(H z), (tH D)⁻¹ * t ∈ (J z).subgroupOf (H z) ∧ t * σ = σ * t := by
  subst hσ
  have hσ3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 :=
    orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂ hcomm
  have hg : (⟨t, t_mem_A⟩ : QA45.originalSubgroup) * qH D (sigma1Nine (z := z) D * σ₂⁻¹) =
      qH D (sigma1Nine (z := z) D * σ₂⁻¹) * ⟨t, t_mem_A⟩ := by
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Commute.mul_right t_commute_sigma1 (Commute.inv_right t_commute_sigma2)).eq
  obtain ⟨s, hs, hsσ⟩ := exists_lift_centralizer D hσ3 hg
  refine ⟨s, ?_, hsσ⟩
  rw [J_mem_iff D, map_mul, map_inv, qH_tH, hs, inv_mul_cancel]

omit [Finite G] in
theorem cosetJ_tH_iff_of_inv_mul_mem {t : ↥(H z)} (ht : (tH D)⁻¹ * t ∈ (J z).subgroupOf (H z))
    (x : G) : cosetJ (z := z) t x ↔ cosetJ (z := z) (tH D) x := by
  have hJ : ((tH D : ↥(H z)) : G)⁻¹ * (t : G) ∈ J z := by
    have := Subgroup.mem_subgroupOf.mp ht
    simpa using this
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨((tH D : ↥(H z)) : G)⁻¹ * t * j, (J z).mul_mem hJ hj, by group⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(((tH D : ↥(H z)) : G)⁻¹ * t)⁻¹ * j, (J z).mul_mem ((J z).inv_mem hJ) hj, by group⟩


theorem exists_lift_tH_commute_sigma_centralizes_J0 (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹) :
    ∃ t : ↥(H z), (tH D)⁻¹ * t ∈ (J z).subgroupOf (H z) ∧ t * σ = σ * t ∧
      ∀ a ∈ CJ z (sigma1Nine (z := z) D : G), (t : G) * a = a * (t : G) := by
  subst hσ
  have hσ3 : orderOf (sigma1Nine (z := z) D * σ₂⁻¹) = 3 :=
    orderOf_mul_inv_of_commute_of_hom (qH D) (sigma1Nine_order D) hσ₂ (qH_sigma1Nine D) hq₂ hcomm
  have hJ0 := J0sub_normal (z := z) (D := D) h hEq hσ₂ hq₂
  have mem_J0 : ∀ {a : G} (ha : a ∈ CJ z (sigma1Nine (z := z) D : G)),
      (⟨a, J_le_H (mem_CJ.mp ha).2⟩ : ↥(H z)) ∈ J0sub D := fun ha =>
    (mem_J0sub_iff' D).mpr ⟨(mem_CJ.mp ha).2,
      Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp ha).1⟩
  have hiP : a2H D ∈ P_H D := a2H_mem_P_H D
  have hiZ : conjZ z (a2H D) = 1 := conjZ_eq_one_of_mem_Q (z := z) D h (a2H D) (qH_a2H_mem_Q D)
  have hqi : qH D (a2H D) = (⟨alpha2, alpha2_mem_A⟩ : QA45.originalSubgroup) := qH_a2H D
  generalize a2H D = i at hiP hiZ hqi
  have hi2 : ∀ a ∈ CJ z (sigma1Nine (z := z) D : G), (i : G) * (i : G) * a =
      a * ((i : G) * (i : G)) := by
    intro a ha
    have haJ : a ∈ J z := (mem_CJ.mp ha).2
    have he := conj_mul_inv_mem_centerIn_of_mem_P_H D h hσ₂ hq₂ hEq hiP ha
    set e := (i : G) * a * (i : G)⁻¹ * a⁻¹ with he_def
    have hie : (i : G) * e * (i : G)⁻¹ = e := by
      have hc := Subgroup.mem_centralizer_singleton_iff.mp
        (centerIn_le_centralizer_of_conjZ_eq_one (z := z) hiZ he)
      calc (i : G) * e * (i : G)⁻¹ = (e * (i : G)) * (i : G)⁻¹ := by rw [hc]
        _ = e := by group
    have hee : e * e = 1 := mul_self_eq_one_of_mem_centerIn_J h he
    have h1 : (i : G) * a * (i : G)⁻¹ = e * a := by rw [he_def]; group
    have h2 : (i : G) * ((i : G) * a * (i : G)⁻¹) * (i : G)⁻¹ = a := by
      calc (i : G) * ((i : G) * a * (i : G)⁻¹) * (i : G)⁻¹ = (i : G) * (e * a) * (i : G)⁻¹ := by
            rw [h1]
        _ = ((i : G) * e * (i : G)⁻¹) * ((i : G) * a * (i : G)⁻¹) := by group
        _ = e * (e * a) := by rw [hie, h1]
        _ = a := by rw [← mul_assoc, hee, one_mul]
    calc (i : G) * (i : G) * a =
        ((i : G) * ((i : G) * a * (i : G)⁻¹) * (i : G)⁻¹) * ((i : G) * (i : G)) := by group
      _ = a * ((i : G) * (i : G)) := by rw [h2]
  set K : Subgroup ↥(H z) := Subgroup.centralizer (J0sub D : Set ↥(H z)) with hK
  have hi2K : i * i ∈ K := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨hyJ, hyc⟩ := (mem_J0sub_iff' D).mp hy
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact (hi2 (y : G) (mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyc, hyJ⟩)).symm
  have hσJ0 : ∀ y ∈ J0sub D, (sigma1Nine (z := z) D * σ₂⁻¹) * y =
      y * (sigma1Nine (z := z) D * σ₂⁻¹) := by
    intro y hy
    obtain ⟨hyJ, hyc⟩ := (mem_J0sub_iff' D).mp hy
    have hyB := CJ_sigma1Nine_le_CJ_mul_inv D hEq
      (mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hyc, hyJ⟩)
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp (mem_CJ.mp hyB).1).symm
  have hrK : ∀ x ∈ K, (sigma1Nine (z := z) D * σ₂⁻¹) * x * (sigma1Nine (z := z) D * σ₂⁻¹)⁻¹ ∈
      K := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    set s := sigma1Nine (z := z) D * σ₂⁻¹ with hs
    have h1 : s * y = y * s := hσJ0 y hy
    have h1' : y * s⁻¹ = s⁻¹ * y := by
      calc y * s⁻¹ = s⁻¹ * (s * y) * s⁻¹ := by group
        _ = s⁻¹ * (y * s) * s⁻¹ := by rw [h1]
        _ = s⁻¹ * y := by group
    have h2 : y * x = x * y := hx y hy
    calc y * (s * x * s⁻¹) = (y * s) * x * s⁻¹ := by group
      _ = (s * y) * x * s⁻¹ := by rw [h1]
      _ = s * (y * x) * s⁻¹ := by group
      _ = s * (x * y) * s⁻¹ := by rw [h2]
      _ = s * x * (y * s⁻¹) := by group
      _ = s * x * (s⁻¹ * y) := by rw [h1']
      _ = s * x * s⁻¹ * y := by group
  have hKJ : ¬ 3 ∣ Nat.card ↥(K ⊓ (J z).subgroupOf (H z)) := by
    intro h3
    have hdvd : Nat.card ↥(K ⊓ (J z).subgroupOf (H z)) ∣ Nat.card ↥((J z).subgroupOf (H z)) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (J_le_H (z := z))).toEquiv, card_J h]
      at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans hdvd)
    omega
  have hqi2 : qH D (i * i) = (⟨t, t_mem_A⟩ : QA45.originalSubgroup) := by
    rw [map_mul, hqi]
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact alpha2_sq
  have hg : qH D (i * i) * qH D (sigma1Nine (z := z) D * σ₂⁻¹) =
      qH D (sigma1Nine (z := z) D * σ₂⁻¹) * qH D (i * i) := by
    rw [hqi2, map_mul, map_inv, qH_sigma1Nine, hq₂]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Commute.mul_right t_commute_sigma1 (Commute.inv_right t_commute_sigma2)).eq
  obtain ⟨s, hsK, hsq, hsσ⟩ := exists_lift_centralizer_of_le D hσ3 hrK hKJ hi2K hg
  refine ⟨s, ?_, hsσ, ?_⟩
  · rw [J_mem_iff D, map_mul, map_inv, qH_tH, hsq, hqi2, inv_mul_cancel]
  · intro a ha
    have hc := Subgroup.mem_centralizer_iff.mp hsK _ (mem_J0 ha)
    exact (congrArg Subtype.val hc).symm

end CFSG.RankThree.GF2n.Parrott

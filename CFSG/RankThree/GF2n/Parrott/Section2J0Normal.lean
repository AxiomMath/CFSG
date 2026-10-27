module

public import CFSG.RankThree.GF2n.Parrott.Section3Lift

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

noncomputable def J0sub : Subgroup ↥(H z) :=
  (centralizerJ (sigma1Nine (z := z) D)).map (Subgroup.inclusion (J_le_H (z := z)))

theorem mem_J0sub_iff {x : ↥(H z)} :
    x ∈ J0sub D ↔ ∃ j : J z, j ∈ centralizerJ (sigma1Nine (z := z) D) ∧
      (Subgroup.inclusion (J_le_H (z := z)) j : ↥(H z)) = x := by
  rw [J0sub, Subgroup.mem_map]

theorem mem_J0sub_iff' {x : ↥(H z)} :
    x ∈ J0sub D ↔ (x : G) ∈ J z ∧
      (x : G) * (sigma1Nine (z := z) D : G) =
        (sigma1Nine (z := z) D : G) * (x : G) := by
  rw [mem_J0sub_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨j.2, ?_⟩
    simpa using (mem_centralizerJ_iff.mp hj)
  · rintro ⟨hxJ, hxc⟩
    refine ⟨⟨(x : G), hxJ⟩, ?_, ?_⟩
    · rw [mem_centralizerJ_iff]
      exact hxc
    · rfl

theorem normalizer_zpowers_le_normalizer_J0sub :
    Subgroup.normalizer (Subgroup.zpowers (sigma1Nine (z := z) D) : Set ↥(H z)) ≤
      Subgroup.normalizer (J0sub D : Set ↥(H z)) := by
  intro n hn
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hx
  change x ∈ J0sub D at hx
  change n * x * n⁻¹ ∈ J0sub D
  rw [mem_J0sub_iff'] at hx ⊢
  obtain ⟨hxJ, hxc⟩ := hx
  have hσ1' : (n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D * n ∈
      Subgroup.zpowers (sigma1Nine (z := z) D) := by
    refine (Subgroup.mem_normalizer_iff.mp hn
      ((n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D * n)).mpr ?_
    have hconj : n * ((n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D * n) * n⁻¹ =
        sigma1Nine (z := z) D := by group
    rw [hconj]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hσ1'
  have hxcommH : x * sigma1Nine (z := z) D = sigma1Nine (z := z) D * x := by
    apply Subtype.ext
    simpa using hxc
  have hxcommC : Commute x (sigma1Nine (z := z) D) := hxcommH
  have hxcomm' : x * ((n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D * n) =
      ((n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D * n) * x := by
    rw [← hk]
    exact hxcommC.zpow_right k
  have hyJ : ((n * x * n⁻¹ : ↥(H z)) : G) ∈ J z := by
    have hxJH : x ∈ (J z).subgroupOf (H z) := (Subgroup.mem_subgroupOf).mpr hxJ
    exact (Subgroup.mem_subgroupOf).mp (hN.conj_mem x hxJH n)
  have hycommH : (n * x * n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D =
      sigma1Nine (z := z) D * (n * x * n⁻¹ : ↥(H z)) := by
    calc (n * x * n⁻¹) * sigma1Nine (z := z) D
        = n * (x * ((n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D * n)) * n⁻¹ := by group
      _ = n * (((n⁻¹ : ↥(H z)) * sigma1Nine (z := z) D * n) * x) * n⁻¹ := by
            rw [hxcomm']
      _ = sigma1Nine (z := z) D * (n * x * n⁻¹) := by group
  refine ⟨hyJ, ?_⟩
  simpa using congrArg Subtype.val hycommH

theorem centralizer_sigma2_le_normalizer_J0sub (σ₂ : ↥(H z))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Subgroup.centralizer ({σ₂} : Set ↥(H z)) ≤
      Subgroup.normalizer (J0sub D : Set ↥(H z)) := by
  intro c hc
  refine Subgroup.mem_normalizer_fintype ?_
  intro x hx
  change x ∈ J0sub D at hx
  change c * x * c⁻¹ ∈ J0sub D
  rw [mem_J0sub_iff'] at hx ⊢
  obtain ⟨hxJ, hxc⟩ := hx
  have hxσ₂ : (x : G) * (σ₂ : G) = (σ₂ : G) * (x : G) := by
    have hx1 : (⟨(x : G), hxJ⟩ : J z) ∈ centralizerJ (sigma1Nine (z := z) D) := by
      rw [mem_centralizerJ_iff]
      exact hxc
    have hx2 : (⟨(x : G), hxJ⟩ : J z) ∈ centralizerJ σ₂ := by
      rw [← hEq]
      exact hx1
    exact mem_centralizerJ_iff.mp hx2
  have hcσ₂H : c * σ₂ = σ₂ * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcσ₂_inv : c⁻¹ * σ₂ = σ₂ * c⁻¹ := by
    have h : Commute c σ₂ := hcσ₂H
    exact (Commute.inv_left_iff.mpr h).eq
  have hxσ₂H : x * σ₂ = σ₂ * x := by
    apply Subtype.ext
    simpa using hxσ₂
  have hyσ₂H : (c * x * c⁻¹ : ↥(H z)) * σ₂ = σ₂ * (c * x * c⁻¹ : ↥(H z)) := by
    calc (c * x * c⁻¹) * σ₂
        = c * (x * (c⁻¹ * σ₂)) := by group
      _ = c * (x * (σ₂ * c⁻¹)) := by rw [hcσ₂_inv]
      _ = c * ((x * σ₂) * c⁻¹) := by group
      _ = c * ((σ₂ * x) * c⁻¹) := by rw [hxσ₂H]
      _ = (c * σ₂) * x * c⁻¹ := by group
      _ = (σ₂ * c) * x * c⁻¹ := by rw [hcσ₂H]
      _ = σ₂ * (c * x * c⁻¹) := by group
  have hyJ : ((c * x * c⁻¹ : ↥(H z)) : G) ∈ J z := by
    have hxJH : x ∈ (J z).subgroupOf (H z) := (Subgroup.mem_subgroupOf).mpr hxJ
    exact (Subgroup.mem_subgroupOf).mp (hN.conj_mem x hxJH c)
  have hyσ₂G : ((c * x * c⁻¹ : ↥(H z)) : G) * (σ₂ : G) =
      (σ₂ : G) * ((c * x * c⁻¹ : ↥(H z)) : G) := by
    simpa using congrArg Subtype.val hyσ₂H
  have hy1 : (⟨((c * x * c⁻¹ : ↥(H z)) : G), hyJ⟩ : J z) ∈
      centralizerJ (sigma1Nine (z := z) D) := by
    rw [hEq]
    rw [mem_centralizerJ_iff]
    exact hyσ₂G
  refine ⟨hyJ, ?_⟩
  simpa using mem_centralizerJ_iff.mp hy1

theorem sup_le_normalizer_J0sub (σ₂ : ↥(H z))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂) :
    Subgroup.normalizer (Subgroup.zpowers (sigma1Nine (z := z) D) : Set ↥(H z)) ⊔
      Subgroup.centralizer ({σ₂} : Set ↥(H z)) ≤
        Subgroup.normalizer (J0sub D : Set ↥(H z)) :=
  sup_le (normalizer_zpowers_le_normalizer_J0sub (D := D))
    (centralizer_sigma2_le_normalizer_J0sub (D := D) σ₂ hEq)

theorem J0sub_normal_of_generation (σ₂ : ↥(H z))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hgen : (Subgroup.normalizer (Subgroup.zpowers (sigma1Nine (z := z) D) : Set ↥(H z)) ⊔
      Subgroup.centralizer ({σ₂} : Set ↥(H z))) ⊔ ((J z).subgroupOf (H z)) = ⊤)
    (hJ : ((J z).subgroupOf (H z)) ≤ Subgroup.normalizer (J0sub D : Set ↥(H z))) :
    (J0sub D).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
  exact sup_le (sup_le_normalizer_J0sub (D := D) σ₂ hEq) hJ

end CFSG.RankThree.GF2n.Parrott

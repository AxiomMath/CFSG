module

public import CFSG.RankThree.GF2n.Parrott.Section5ChoiceT1
public import CFSG.RankThree.GF2n.Parrott.Section5ChoiceS0
public import CFSG.RankThree.GF2n.Parrott.Section5SigmaThree

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem exists_parrott_T1_choice (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2) :
    ∃ (T₁ S₀ : Subgroup G) (t : G) (σ₂ : ↥(H z)),
      IsSylowOf 2 T₁ (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G)) ∧
      IsSylowOf 2 S₀
        (H z ⊓ normalizer (zpowers ((sigma1Nine (z := z) D : ↥(H z)) : G) : Set G)) ∧
      T₁ ≤ S₀ ∧ t ∈ centerIn T₁ ∧ t ∉ J z ∧
      (∀ e ∈ centerIn S₀, e = 1 ∨ e = z ∨ e = t * z₁ ∨ e = t * z₁ * z) ∧
      (∃ y ∈ S₀, y ∉ centralizer ({z₁} : Set G)) ∧
      orderOf σ₂ = 3 ∧ qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂ ∧
      (σ₂ : G) * t = t * (σ₂ : G) ∧
      (∃ ht : t ∈ H z, qH (z := z) D ⟨t, ht⟩ =
        (⟨CFSG.RankThree.GF2n.Parrott.t, t_mem_A⟩ :
          QA45.originalSubgroup)) ∧
      t * z₁ ∈ centerIn S₀ := by
  obtain ⟨T₁, hT₁, hmap⟩ := exists_isSylowOf_centralizer_sigma1Nine_map_eq D h
  obtain ⟨σ₂, hσ₂, hq₂, hc₂⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  obtain ⟨S₀, hS₀, hTS, y, hyS, hy⟩ :=
    exists_isSylowOf_normalizer_sigma1Nine_not_le_centralizer_z1 D h hZ hz₁ hz₁z hord hT₁
  obtain ⟨t, htT, htJ, hZS⟩ :=
    exists_mem_centerIn_forall_mem_centerIn_eq D h hz₁ hz₁z hord hT₁ hmap hS₀ hTS hyS hy
  have htH : t ∈ H z := (hT₁.le htT.1).1
  exact ⟨T₁, S₀, t, σ₂, hT₁, hS₀, hTS, htT, htJ, hZS, ⟨y, hyS, hy⟩, hσ₂, hq₂, hc₂,
    commute_of_mem_centerIn_of_map_eq D h hT₁ hmap hσ₂ hq₂ hc₂ t htT,
    ⟨htH, qH_eq_t_of_mem_of_map_eq D hmap (x := ⟨t, htH⟩) htT.1
      (mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine D h hT₁ t htT) htJ⟩,
    mul_z1_mem_centerIn_of_forall_mem_centerIn_eq D h hz₁ hz₁z hord hT₁ hmap hS₀ hTS hyS hy
      htT htJ hZS⟩

theorem exists_elementaryAbelian_or_isSylowOf_centralizer_sigma1Nine_mul
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z))
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH (z := z) D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) :
    (∃ E : Subgroup G,
        E ≤ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G) ∧
        Nat.card E = 16 ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1) ∨
      ∃ T : Subgroup G,
        IsSylowOf 2 T (centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G)) ∧
        Nat.card T = 2 ^ 5 := by
  obtain ⟨T₁, hT₁, hmap⟩ := exists_isSylowOf_centralizer_sigma1Nine_map_eq D h
  obtain ⟨x, hxZ, hxJ⟩ :=
    exists_mem_centerIn_not_mem_J_of_isSylowOf_centralizer_sigma1Nine D h hT₁
  have hxH : x ∈ H z := (hT₁.le hxZ.1).1
  have hx2 : x * x = 1 :=
    mul_self_eq_one_of_mem_centerIn_isSylowOf_centralizer_sigma1Nine D h hT₁ x hxZ
  have hqx : qH (z := z) D ⟨x, hxH⟩ = (⟨t, t_mem_A⟩ : QA45.originalSubgroup) :=
    qH_eq_t_of_mem_of_map_eq D hmap (x := ⟨x, hxH⟩) hxZ.1 hx2 hxJ
  have hx₁ : x * ((sigma1Nine (z := z) D : ↥(H z)) : G) =
      ((sigma1Nine (z := z) D : ↥(H z)) : G) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (hT₁.le hxZ.1).2
  have hx₂ : (σ₂ : G) * x = x * (σ₂ : G) :=
    commute_of_mem_centerIn_of_map_eq D h hT₁ hmap hσ₂ hq₂ hc₂ x hxZ
  have hxσ : x ∈ centralizer ({((sigma1Nine (z := z) D * σ₂ : ↥(H z)) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul]
    calc x * (((sigma1Nine (z := z) D : ↥(H z)) : G) * (σ₂ : G))
        = (x * ((sigma1Nine (z := z) D : ↥(H z)) : G)) * (σ₂ : G) := by group
      _ = (((sigma1Nine (z := z) D : ↥(H z)) : G) * x) * (σ₂ : G) := by rw [hx₁]
      _ = ((sigma1Nine (z := z) D : ↥(H z)) : G) * (x * (σ₂ : G)) := by group
      _ = ((sigma1Nine (z := z) D : ↥(H z)) : G) * ((σ₂ : G) * x) := by rw [hx₂]
      _ = (((sigma1Nine (z := z) D : ↥(H z)) : G) * (σ₂ : G)) * x := by group
  exact exists_elementaryAbelian_or_isSylowOf_centralizer_sigma1Nine_mul_of_involution D h hZ
    hIII hσ₂ hq₂ hc₂ (τ := ⟨x, hxH⟩) hx2 hqx hxσ

end CFSG.RankThree.GF2n.Parrott

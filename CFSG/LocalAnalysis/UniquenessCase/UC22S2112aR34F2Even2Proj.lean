module

public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
private lemma uc22s2112r34_proj_commute {K₁ K₂ : Subgroup X} (hc : ⁅K₁, K₂⁆ = ⊥) :
    ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x := by
  intro x hx y hy
  have hcent : K₁ ≤ Subgroup.centralizer (K₂ : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc
  exact ((Subgroup.mem_centralizer_iff.mp (hcent hx)) y hy).symm

omit [Finite X] in
private lemma uc22s2112r34_proj_mul_comm_of_coe_mul_eq {A B C : Subgroup X}
    (h : (A : Set X) * (B : Set X) = (C : Set X)) :
    (A : Set X) * (B : Set X) = (B : Set X) * (A : Set X) := by
  have hinv : ((A : Set X) * (B : Set X))⁻¹ = (B : Set X) * (A : Set X) := by
    ext x
    rw [Set.mem_inv, Set.mem_mul, Set.mem_mul]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha,
        by rw [← mul_inv_rev, hab, inv_inv]⟩
    · rintro ⟨b, hb, a, ha, hba⟩
      exact ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb,
        by rw [← mul_inv_rev, hba]⟩
  rw [← hinv, h, inv_coe_set]

private lemma uc22s2112r34_proj_inf_le_sylow {K₁ K₂ P : Subgroup X}
    (hc : ⁅K₁, K₂⁆ = ⊥) (hKK : IsPGroup 2 ↥(K₁ ⊓ K₂))
    (hQ₁ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₁) K₁)
    (hQ₂ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₂) K₂) :
    K₁ ⊓ K₂ ≤ P ⊓ K₁ ∧ K₁ ⊓ K₂ ≤ P ⊓ K₂ ∧
      (P ⊓ K₁) ⊓ (P ⊓ K₂) = K₁ ⊓ K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := uc22s2112r34_proj_commute hc
  have hnorm₁ : K₁ ⊓ K₂ ≤ Subgroup.normalizer ((P ⊓ K₁ : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx q hq
    have hxq : x * q * x⁻¹ = q := by
      calc x * q * x⁻¹ = q * x * x⁻¹ := by rw [hcomm q hq.2 x hx.2]
        _ = q := by group
    rwa [hxq]
  have hsup₁ : IsPGroup 2 ↥((P ⊓ K₁) ⊔ (K₁ ⊓ K₂)) :=
    IsPGroup.to_sup_of_normal_left' hQ₁.isPGroup hKK hnorm₁
  have heq₁ : (P ⊓ K₁) ⊔ (K₁ ⊓ K₂) = P ⊓ K₁ :=
    hQ₁.eq_of_le le_sup_left (sup_le inf_le_right inf_le_left) hsup₁
  have hle₁ : K₁ ⊓ K₂ ≤ P ⊓ K₁ := by
    rw [← heq₁]
    exact le_sup_right
  have hnorm₂ : K₁ ⊓ K₂ ≤ Subgroup.normalizer ((P ⊓ K₂ : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx q hq
    have hxq : x * q * x⁻¹ = q := by
      calc x * q * x⁻¹ = q * x * x⁻¹ := by rw [hcomm x hx.1 q hq.2]
        _ = q := by group
    rwa [hxq]
  have hsup₂ : IsPGroup 2 ↥((P ⊓ K₂) ⊔ (K₁ ⊓ K₂)) :=
    IsPGroup.to_sup_of_normal_left' hQ₂.isPGroup hKK hnorm₂
  have heq₂ : (P ⊓ K₂) ⊔ (K₁ ⊓ K₂) = P ⊓ K₂ :=
    hQ₂.eq_of_le le_sup_left (sup_le inf_le_right inf_le_right) hsup₂
  have hle₂ : K₁ ⊓ K₂ ≤ P ⊓ K₂ := by
    rw [← heq₂]
    exact le_sup_right
  refine ⟨hle₁, hle₂, le_antisymm ?_ (le_inf hle₁ hle₂)⟩
  exact inf_le_inf inf_le_right inf_le_right

private lemma uc22s2112r34_proj_isSylow_sup {K₁ K₂ P : Subgroup X}
    (hc : ⁅K₁, K₂⁆ = ⊥) (hKK : IsPGroup 2 ↥(K₁ ⊓ K₂))
    (hQ₁ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₁) K₁)
    (hQ₂ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₂) K₂) :
    CFSG.ABGLocalTools.IsSylowOf 2 ((P ⊓ K₁) ⊔ (P ⊓ K₂)) (K₁ ⊔ K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := uc22s2112r34_proj_commute hc
  obtain ⟨-, -, hQinf⟩ := uc22s2112r34_proj_inf_le_sylow hc hKK hQ₁ hQ₂
  have hQcomm : ∀ x ∈ P ⊓ K₁, ∀ y ∈ P ⊓ K₂, x * y = y * x := by
    intro x hx y hy
    exact hcomm x hx.2 y hy.2
  have hnorm : (P ⊓ K₂ : Subgroup X) ≤
      Subgroup.normalizer ((P ⊓ K₁ : Subgroup X) : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    have hyx : y * x * y⁻¹ = x := by
      calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [(hcomm x hx.2 y hy.2).symm]
        _ = x := by group
    rwa [hyx]
  have hQp : IsPGroup 2 ↥((P ⊓ K₁) ⊔ (P ⊓ K₂)) :=
    IsPGroup.to_sup_of_normal_left' hQ₁.isPGroup hQ₂.isPGroup hnorm
  have hNcard : Nat.card ↥(K₁ ⊔ K₂) * Nat.card ↥(K₁ ⊓ K₂) =
      Nat.card ↥K₁ * Nat.card ↥K₂ :=
    (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute K₁ K₂ hcomm).1
  have hQcard : Nat.card ↥((P ⊓ K₁) ⊔ (P ⊓ K₂)) * Nat.card ↥(K₁ ⊓ K₂) =
      Nat.card ↥(P ⊓ K₁) * Nat.card ↥(P ⊓ K₂) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (P ⊓ K₁) (P ⊓ K₂) hQcomm).1
    rwa [hQinf] at h
  have hQle : ((P ⊓ K₁) ⊔ (P ⊓ K₂) : Subgroup X) ≤ K₁ ⊔ K₂ :=
    sup_le (inf_le_right.trans le_sup_left) (inf_le_right.trans le_sup_right)
  have hrel : ((P ⊓ K₁) ⊔ (P ⊓ K₂) : Subgroup X).relIndex (K₁ ⊔ K₂) =
      (P ⊓ K₁).relIndex K₁ * (P ⊓ K₂).relIndex K₂ := by
    have h1 := Subgroup.relIndex_mul_card (H := (P ⊓ K₁) ⊔ (P ⊓ K₂))
      (K := K₁ ⊔ K₂)
    rw [inf_eq_left.mpr hQle] at h1
    have h2 := Subgroup.relIndex_mul_card (H := P ⊓ K₁) (K := K₁)
    rw [inf_eq_left.mpr hQ₁.le] at h2
    have h3 := Subgroup.relIndex_mul_card (H := P ⊓ K₂) (K := K₂)
    rw [inf_eq_left.mpr hQ₂.le] at h3
    have hmul : ((P ⊓ K₁) ⊔ (P ⊓ K₂) : Subgroup X).relIndex (K₁ ⊔ K₂) *
        (Nat.card ↥((P ⊓ K₁) ⊔ (P ⊓ K₂)) * Nat.card ↥(K₁ ⊓ K₂)) =
        ((P ⊓ K₁).relIndex K₁ * (P ⊓ K₂).relIndex K₂) *
          (Nat.card ↥((P ⊓ K₁) ⊔ (P ⊓ K₂)) * Nat.card ↥(K₁ ⊓ K₂)) := by
      calc
        ((P ⊓ K₁) ⊔ (P ⊓ K₂) : Subgroup X).relIndex (K₁ ⊔ K₂) *
            (Nat.card ↥((P ⊓ K₁) ⊔ (P ⊓ K₂)) * Nat.card ↥(K₁ ⊓ K₂)) =
            (((P ⊓ K₁) ⊔ (P ⊓ K₂) : Subgroup X).relIndex (K₁ ⊔ K₂) *
              Nat.card ↥((P ⊓ K₁) ⊔ (P ⊓ K₂))) * Nat.card ↥(K₁ ⊓ K₂) := by
              ring
        _ = Nat.card ↥(K₁ ⊔ K₂) * Nat.card ↥(K₁ ⊓ K₂) := by rw [h1]
        _ = Nat.card ↥K₁ * Nat.card ↥K₂ := hNcard
        _ = ((P ⊓ K₁).relIndex K₁ * Nat.card ↥(P ⊓ K₁)) *
              ((P ⊓ K₂).relIndex K₂ * Nat.card ↥(P ⊓ K₂)) := by rw [h2, h3]
        _ = ((P ⊓ K₁).relIndex K₁ * (P ⊓ K₂).relIndex K₂) *
              (Nat.card ↥(P ⊓ K₁) * Nat.card ↥(P ⊓ K₂)) := by ring
        _ = ((P ⊓ K₁).relIndex K₁ * (P ⊓ K₂).relIndex K₂) *
              (Nat.card ↥((P ⊓ K₁) ⊔ (P ⊓ K₂)) * Nat.card ↥(K₁ ⊓ K₂)) := by
              rw [← hQcard]
    exact Nat.eq_of_mul_eq_mul_right
      (Nat.mul_pos Nat.card_pos Nat.card_pos) hmul
  have hodd : ¬ 2 ∣ ((P ⊓ K₁) ⊔ (P ⊓ K₂) : Subgroup X).relIndex (K₁ ⊔ K₂) := by
    rw [hrel]
    intro h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hQ₁).2.2 h
    · exact (CFSG.ABGLocalTools.isSylowOf_iff.mp hQ₂).2.2 h
  exact (CFSG.ABGLocalTools.isSylowOf_iff).mpr ⟨hQle, hQp, hodd⟩

private lemma uc22s2112r34_proj_inf_sup_eq {K₁ K₂ P : Subgroup X}
    (hc : ⁅K₁, K₂⁆ = ⊥) (hKK : IsPGroup 2 ↥(K₁ ⊓ K₂))
    (hP : IsPGroup 2 ↥P)
    (hQ₁ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₁) K₁)
    (hQ₂ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₂) K₂) :
    P ⊓ (K₁ ⊔ K₂) = (P ⊓ K₁) ⊔ (P ⊓ K₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSyl := uc22s2112r34_proj_isSylow_sup hc hKK hQ₁ hQ₂
  have hle : (P ⊓ K₁) ⊔ (P ⊓ K₂) ≤ P ⊓ (K₁ ⊔ K₂) :=
    sup_le (le_inf inf_le_left (inf_le_right.trans le_sup_left))
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))
  exact hSyl.eq_of_le hle inf_le_right hP.to_inf_left

private lemma uc22s2112r34_proj_inf_sup_eq_mul {K₁ K₂ P R : Subgroup X}
    (hc : ⁅K₁, K₂⁆ = ⊥) (hKK : IsPGroup 2 ↥(K₁ ⊓ K₂))
    (hP : IsPGroup 2 ↥P)
    (hQ₁ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₁) K₁)
    (hQ₂ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₂) K₂)
    (hR : R = (R ⊓ K₁) ⊔ (R ⊓ K₂))
    (hRP : (R : Set X) * (P : Set X) = (P : Set X) * (R : Set X)) :
    ((((R ⊔ P) ⊓ (K₁ ⊔ K₂)) ⊓ K₁ : Subgroup X) : Set X) =
      ((R ⊓ K₁ : Subgroup X) : Set X) * ((P ⊓ K₁ : Subgroup X) : Set X) := by
  have hcomm := uc22s2112r34_proj_commute hc
  obtain ⟨hKinfQ₁, -, -⟩ := uc22s2112r34_proj_inf_le_sylow hc hKK hQ₁ hQ₂
  have hPinf : P ⊓ (K₁ ⊔ K₂) = (P ⊓ K₁) ⊔ (P ⊓ K₂) :=
    uc22s2112r34_proj_inf_sup_eq hc hKK hP hQ₁ hQ₂
  have hRcomm : ∀ x ∈ R ⊓ K₁, ∀ y ∈ R ⊓ K₂, x * y = y * x := by
    intro x hx y hy
    exact hcomm x hx.2 y hy.2
  have hRcoe : (R : Set X) =
      ((R ⊓ K₁ : Subgroup X) : Set X) * ((R ⊓ K₂ : Subgroup X) : Set X) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (R ⊓ K₁) (R ⊓ K₂) hRcomm).2
    calc (R : Set X) = (((R ⊓ K₁) ⊔ (R ⊓ K₂) : Subgroup X) : Set X) :=
          congrArg (fun S : Subgroup X => (S : Set X)) hR
      _ = ((R ⊓ K₁ : Subgroup X) : Set X) * ((R ⊓ K₂ : Subgroup X) : Set X) := h
  have hQcomm : ∀ x ∈ P ⊓ K₁, ∀ y ∈ P ⊓ K₂, x * y = y * x := by
    intro x hx y hy
    exact hcomm x hx.2 y hy.2
  have hQcoe : ((P ⊓ (K₁ ⊔ K₂) : Subgroup X) : Set X) =
      ((P ⊓ K₁ : Subgroup X) : Set X) * ((P ⊓ K₂ : Subgroup X) : Set X) := by
    rw [hPinf]
    exact (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (P ⊓ K₁) (P ⊓ K₂) hQcomm).2
  have hRN : R ≤ K₁ ⊔ K₂ := by
    calc R = (R ⊓ K₁) ⊔ (R ⊓ K₂) := hR
      _ ≤ K₁ ⊔ K₂ :=
        sup_le (fun _ hx => Subgroup.mem_sup_left hx.2)
          (fun _ hx => Subgroup.mem_sup_right hx.2)
  have hHcoe : (((R ⊔ P) ⊓ (K₁ ⊔ K₂) : Subgroup X) : Set X) =
      (R : Set X) * ((P ⊓ (K₁ ⊔ K₂) : Subgroup X) : Set X) := by
    have h1 : ((R ⊔ P : Subgroup X) : Set X) = (R : Set X) * (P : Set X) :=
      CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hRP
    rw [Subgroup.coe_inf, h1, ← Subgroup.mul_inf_assoc R P (K₁ ⊔ K₂) hRN]
  ext x
  constructor
  · intro hx
    change x ∈ (((R ⊔ P) ⊓ (K₁ ⊔ K₂)) ⊓ K₁ : Subgroup X) at hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxH, hxK₁⟩ := hx
    change x ∈ (((R ⊔ P) ⊓ (K₁ ⊔ K₂) : Subgroup X) : Set X) at hxH
    rw [hHcoe] at hxH
    obtain ⟨r, hr, p, hp, rfl⟩ := hxH
    rw [hRcoe] at hr
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := hr
    rw [hQcoe] at hp
    obtain ⟨q₁, hq₁, q₂, hq₂, rfl⟩ := hp
    have hr₂q₁ : r₂ * q₁ = q₁ * r₂ := (hcomm q₁ hq₁.2 r₂ hr₂.2).symm
    have hxeq : (r₁ * r₂) * (q₁ * q₂) = (r₁ * q₁) * (r₂ * q₂) := by
      calc (r₁ * r₂) * (q₁ * q₂) = r₁ * (r₂ * (q₁ * q₂)) := by group
        _ = r₁ * ((r₂ * q₁) * q₂) := by group
        _ = r₁ * ((q₁ * r₂) * q₂) := by rw [hr₂q₁]
        _ = (r₁ * q₁) * (r₂ * q₂) := by group
    have haK₁ : r₁ * q₁ ∈ K₁ := K₁.mul_mem hr₁.2 hq₁.2
    have hbK₂ : r₂ * q₂ ∈ K₂ := K₂.mul_mem hr₂.2 hq₂.2
    have hbK₁ : r₂ * q₂ ∈ K₁ := by
      have h := K₁.mul_mem (K₁.inv_mem haK₁) hxK₁
      have h2 : (r₁ * q₁)⁻¹ * ((r₁ * q₁) * (r₂ * q₂)) ∈ K₁ := by
        rw [← hxeq]
        exact h
      have he : r₂ * q₂ = (r₁ * q₁)⁻¹ * ((r₁ * q₁) * (r₂ * q₂)) := by group
      rwa [he]
    have hbQ₁ : r₂ * q₂ ∈ P ⊓ K₁ := hKinfQ₁ ⟨hbK₁, hbK₂⟩
    refine Set.mem_mul.mpr ⟨r₁, hr₁, q₁ * (r₂ * q₂),
      (P ⊓ K₁).mul_mem hq₁ hbQ₁, ?_⟩
    calc r₁ * (q₁ * (r₂ * q₂)) = (r₁ * q₁) * (r₂ * q₂) := by group
      _ = (r₁ * r₂) * (q₁ * q₂) := hxeq.symm
  · rw [Set.mem_mul]
    rintro ⟨r₁, hr₁, q₁, hq₁, rfl⟩
    change r₁ * q₁ ∈ (((R ⊔ P) ⊓ (K₁ ⊔ K₂)) ⊓ K₁ : Subgroup X)
    rw [Subgroup.mem_inf]
    refine ⟨?_, K₁.mul_mem hr₁.2 hq₁.2⟩
    rw [Subgroup.mem_inf]
    exact ⟨(R ⊔ P).mul_mem (Subgroup.mem_sup_left hr₁.1)
      (Subgroup.mem_sup_right hq₁.1),
      (K₁ ⊔ K₂).mul_mem (Subgroup.mem_sup_left hr₁.2) (Subgroup.mem_sup_left hq₁.2)⟩

private lemma uc22s2112r34_proj_eq_bot_of_odd_isPGroup {T : Subgroup X}
    (hT : IsPGroup 2 ↥T) (hodd : Odd (Nat.card T)) : T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hk0 : k = 0 := by
    by_contra hk0
    exact hodd.not_two_dvd_nat (hk ▸ dvd_pow_self 2 hk0)
  exact Subgroup.eq_bot_of_card_eq T (by rw [hk, hk0, pow_zero])

theorem uc22s2112r34_proj_permutes {K₁ K₂ P R : Subgroup X} (hc : ⁅K₁, K₂⁆ = ⊥)
    (hKK : IsPGroup 2 ↥(K₁ ⊓ K₂)) (hP : IsPGroup 2 ↥P)
    (hQ₁ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₁) K₁)
    (hQ₂ : CFSG.ABGLocalTools.IsSylowOf 2 (P ⊓ K₂) K₂) (hR : R = (R ⊓ K₁) ⊔ (R ⊓ K₂))
    (hRP : (R : Set X) * (P : Set X) = (P : Set X) * (R : Set X)) :
    ((R ⊓ K₁ : Subgroup X) : Set X) * ((P ⊓ K₁ : Subgroup X) : Set X) =
      ((P ⊓ K₁ : Subgroup X) : Set X) * ((R ⊓ K₁ : Subgroup X) : Set X) := by
  exact uc22s2112r34_proj_mul_comm_of_coe_mul_eq
    (uc22s2112r34_proj_inf_sup_eq_mul hc hKK hP hQ₁ hQ₂ hR hRP).symm

theorem uc22s2112r34_eq_bot_of_swap {K₁ K₂ P R : Subgroup X} (hc : ⁅K₁, K₂⁆ = ⊥)
    (hKK : IsPGroup 2 ↥(K₁ ⊓ K₂)) (hP : IsPGroup 2 ↥P) {w : X} (hw : w ∈ P)
    (hwK : K₁.map (MulAut.conj w).toMonoidHom = K₂) (hRo : Odd (Nat.card R)) (hRK : R ≤ K₁)
    (hRP : (R : Set X) * (P : Set X) = (P : Set X) * (R : Set X)) : R = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := uc22s2112r34_proj_commute hc
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hRPbot : R ⊓ P = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hRo)
  let S : Subgroup X := R.map (MulAut.conj w).toMonoidHom
  have hScard : Nat.card S = Nat.card R := by
    dsimp [S]
    rw [Subgroup.card_map_of_injective]
    exact (MulAut.conj w).injective
  have hSK₂ : S ≤ K₂ := by
    rw [← hwK]
    exact Subgroup.map_mono hRK
  have hSP : S ≤ R ⊔ P := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    change (MulAut.conj w) r ∈ R ⊔ P
    rw [MulAut.conj_apply]
    exact (R ⊔ P).mul_mem ((R ⊔ P).mul_mem (Subgroup.mem_sup_right hw)
      (Subgroup.mem_sup_left hr)) (Subgroup.mem_sup_right (P.inv_mem hw))
  have hRSbot : R ⊓ S = ⊥ := by
    refine uc22s2112r34_proj_eq_bot_of_odd_isPGroup (T := R ⊓ S) ?_ ?_
    · exact hKK.to_le (inf_le_inf hRK hSK₂)
    · exact Odd.of_dvd_nat hRo (Subgroup.card_dvd_of_le inf_le_left)
  have hRScomm : ∀ x ∈ R, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    exact hcomm x (hRK hx) y (hSK₂ hy)
  have hRScard : Nat.card ↥(R ⊔ S) = Nat.card R * Nat.card R := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute R S hRScomm).1
    simpa [hRSbot, hScard] using h
  have hRPcard : Nat.card ↥(R ⊔ P) = Nat.card R * Nat.card P :=
    CFSG.Quasithin.H23P4.card_eq_mul_of_coe_eq_mul
      (CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hRP) hRPbot
  have hle : R ⊔ S ≤ R ⊔ P := sup_le le_sup_left hSP
  have hdvd : Nat.card R ∣ Nat.card P := by
    have hcarddvd : Nat.card ↥(R ⊔ S) ∣ Nat.card ↥(R ⊔ P) :=
      Subgroup.card_dvd_of_le hle
    rw [hRScard, hRPcard] at hcarddvd
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hcarddvd
  rw [hk] at hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hi0 : i = 0 := by
    by_contra hi0
    exact hRo.not_two_dvd_nat (hi ▸ dvd_pow_self 2 hi0)
  exact Subgroup.eq_bot_of_card_eq R (by rw [hi, hi0, pow_zero])

theorem uc22s2112r34_eq_sup_of_split {K₁ K₂ R : Subgroup X} (hc : ⁅K₁, K₂⁆ = ⊥)
    (h₁ : R = (R ⊓ K₁) ⊔ (R ⊓ centralizer (K₁ : Set X)))
    (h₂ : R = (R ⊓ K₂) ⊔ (R ⊓ centralizer (K₂ : Set X)))
    (hR : ∀ y ∈ R, y ∈ centralizer (K₁ : Set X) → y ∈ centralizer (K₂ : Set X) → y = 1) :
    R = (R ⊓ K₁) ⊔ (R ⊓ K₂) := by
  have hK₂ : K₂ ≤ centralizer (K₁ : Set X) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hc
  have hcomm : ∀ x ∈ R ⊓ K₂, ∀ y ∈ R ⊓ centralizer (K₂ : Set X), x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 hy.2 x hx.2
  have hcoe := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2
  have hsub : R ⊓ centralizer (K₁ : Set X) ≤ R ⊓ K₂ := by
    intro y hy
    have hy2 : y ∈ ((R ⊓ K₂ ⊔ R ⊓ centralizer (K₂ : Set X) : Subgroup X) : Set X) := by
      rw [SetLike.mem_coe, ← h₂]
      exact hy.1
    rw [hcoe] at hy2
    obtain ⟨a, ha, b, hb, rfl⟩ := hy2
    dsimp only at hy ⊢
    have hbC : b ∈ centralizer (K₁ : Set X) := by
      have h := (centralizer (K₁ : Set X)).mul_mem
        ((centralizer (K₁ : Set X)).inv_mem (hK₂ ha.2)) hy.2
      rwa [inv_mul_cancel_left] at h
    rw [hR b hb.1 hbC hb.2, mul_one]
    exact ha
  apply le_antisymm _ (sup_le inf_le_left inf_le_left)
  calc R = R ⊓ K₁ ⊔ R ⊓ centralizer (K₁ : Set X) := h₁
    _ ≤ R ⊓ K₁ ⊔ R ⊓ K₂ := sup_le_sup_left hsub _

end CFSG.LocalAnalysis.UniquenessCase.UC22

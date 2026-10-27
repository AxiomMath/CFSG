module

public import CFSG.RankThree.PartOne.S11d.FinalSylow

public section

namespace CFSG.RankThree.PartOne

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

variable {G : Type*} [Group G] [Finite G]

theorem card_mul_prime_le_of_centralized {p : ℕ} [Fact p.Prime] {J S₀ Q : Subgroup G}
    (hS₀ : IsSylowOf p S₀ J) (hc₀ : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y = y * x) {u : G}
    (huJ : u ∈ normalizer (J : Set G)) (hu₀ : u ∈ normalizer (S₀ : Set G)) (hup : u ^ p = 1)
    (hmove : ∃ s ∈ S₀, u * s * u⁻¹ ≠ s) (hQJ : Q ≤ J) (hQp : IsPGroup p Q)
    (hQu : ∀ q ∈ Q, u * q * u⁻¹ = q) : Nat.card Q * p ≤ Nat.card S₀ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hcardS : Nat.card S₀ = p ^ (Nat.card J).factorization p := hS₀.card_eq
  have hdvd : Nat.card Q ∣ Nat.card J := Subgroup.card_dvd_of_le hQJ
  have hkle : k ≤ (Nat.card J).factorization p := by
    rw [hk] at hdvd
    exact ((Nat.Prime.pow_dvd_iff_le_factorization (Fact.out : p.Prime)
      Nat.card_pos.ne').mp hdvd)
  by_cases heq : k = (Nat.card J).factorization p
  · exfalso
    have hQS : IsSylowOf p Q J := isSylowOf_of_card hQJ (by rw [hk, heq])
    exact not_centralizes_sylow hS₀ hQS hc₀ huJ hu₀ hup hmove hQu
  · have hlt : k + 1 ≤ (Nat.card J).factorization p := by omega
    rw [hk, hcardS, ← pow_succ]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hlt

theorem factorization_eq_of_common_fixed {p : ℕ} [Fact p.Prime] {J₁ J₂ E : Subgroup G}
    {u₁ u₂ y₁ y₂ : G} (hS₁ : IsSylowOf p (zpowers y₁) J₁) (hS₂ : IsSylowOf p (zpowers y₂) J₂)
    (hJ₁ : u₁ ∈ normalizer (J₁ : Set G)) (hJ₂ : u₂ ∈ normalizer (J₂ : Set G))
    (hu₁ : u₁ ∈ normalizer ((zpowers y₁ : Subgroup G) : Set G))
    (hu₂ : u₂ ∈ normalizer ((zpowers y₂ : Subgroup G) : Set G)) (hup₁ : u₁ ^ p = 1)
    (hup₂ : u₂ ^ p = 1) (hmove₁ : u₁ * y₁ * u₁⁻¹ ≠ y₁) (hmove₂ : u₂ * y₂ * u₂⁻¹ ≠ y₂)
    (hE₁ : E ≤ J₁) (hE₂ : E ≤ J₂) (hEu₁ : ∀ e ∈ E, u₁ * e * u₁⁻¹ = e)
    (hEu₂ : ∀ e ∈ E, u₂ * e * u₂⁻¹ = e) (hy₁ : y₁ ^ p ∈ E) (hy₂ : y₂ ^ p ∈ E) :
    (Nat.card J₁).factorization p = (Nat.card J₂).factorization p := by
  have hp : p.Prime := Fact.out
  have hcomm : ∀ y : G, ∀ x ∈ zpowers y, ∀ z ∈ zpowers y, x * z = z * x := by
    intro y x hx z hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_zpow_self y i j).eq
  have hord₁ : orderOf y₁ = p ^ (Nat.card J₁).factorization p := by
    rw [← Nat.card_zpowers]
    exact hS₁.card_eq
  have hord₂ : orderOf y₂ = p ^ (Nat.card J₂).factorization p := by
    rw [← Nat.card_zpowers]
    exact hS₂.card_eq
  have hn₁ : 1 ≤ (Nat.card J₁).factorization p := by
    by_contra hlt
    push Not at hlt
    have h0 : (Nat.card J₁).factorization p = 0 := by omega
    rw [h0, pow_zero, orderOf_eq_one_iff] at hord₁
    apply hmove₁
    rw [hord₁]
    simp
  have hn₂ : 1 ≤ (Nat.card J₂).factorization p := by
    by_contra hlt
    push Not at hlt
    have h0 : (Nat.card J₂).factorization p = 0 := by omega
    rw [h0, pow_zero, orderOf_eq_one_iff] at hord₂
    apply hmove₂
    rw [hord₂]
    simp
  have hz₁ : orderOf (y₁ ^ p) = p ^ ((Nat.card J₁).factorization p - 1) :=
    orderOf_pow_prime_of_eq hp hn₁ hord₁
  have hz₂ : orderOf (y₂ ^ p) = p ^ ((Nat.card J₂).factorization p - 1) :=
    orderOf_pow_prime_of_eq hp hn₂ hord₂
  have h21 : Nat.card (zpowers (y₂ ^ p)) * p ≤ Nat.card (zpowers y₁) :=
    card_mul_prime_le_of_centralized hS₁ (hcomm y₁) hJ₁ hu₁ hup₁ ⟨y₁, mem_zpowers y₁, hmove₁⟩
      (zpowers_le.mpr (hE₁ hy₂)) (isPGroup_zpowers_of_orderOf ⟨_, hz₂⟩)
      (fun q hq => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hq
        rw [← conj_zpow, hEu₁ _ hy₂])
  have h12 : Nat.card (zpowers (y₁ ^ p)) * p ≤ Nat.card (zpowers y₂) :=
    card_mul_prime_le_of_centralized hS₂ (hcomm y₂) hJ₂ hu₂ hup₂ ⟨y₂, mem_zpowers y₂, hmove₂⟩
      (zpowers_le.mpr (hE₂ hy₁)) (isPGroup_zpowers_of_orderOf ⟨_, hz₁⟩)
      (fun q hq => by
        obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hq
        rw [← conj_zpow, hEu₂ _ hy₁])
  rw [Nat.card_zpowers, Nat.card_zpowers, hz₂, hord₁] at h21
  rw [Nat.card_zpowers, Nat.card_zpowers, hz₁, hord₂] at h12
  have e₁ : p ^ ((Nat.card J₁).factorization p - 1) * p = p ^ (Nat.card J₁).factorization p := by
    rw [← pow_succ]
    congr 1
    omega
  have e₂ : p ^ ((Nat.card J₂).factorization p - 1) * p = p ^ (Nat.card J₂).factorization p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e₂] at h21
  rw [e₁] at h12
  exact le_antisymm ((Nat.pow_le_pow_iff_right hp.one_lt).mp h12)
    ((Nat.pow_le_pow_iff_right hp.one_lt).mp h21)

end CFSG.RankThree.PartOne

module

public import CFSG.Quasithin.H13.GoldschmidtQ8SqE9Syl

public section

namespace CFSG.Quasithin.H13.Q8SqE9

open QuaternionGroup Subgroup

variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

namespace Cfg

theorem exists_one (h : Cfg A B) {Y : Subgroup G} (hY9 : Nat.card Y = 9)
    (hYN : ∀ y ∈ Y, y ∈ normalizer (A : Set G) ∧ y ∈ normalizer (B : Set G))
    (hYodd : ∀ y ∈ Y, Odd (orderOf y))
    (hY1 : ∀ y ∈ Y, (∀ q ∈ A ⊔ B, q * y = y * q) → y = 1) :
    ∃ y ∈ Y, orderOf y = 3 ∧ (∀ b ∈ B, y * b = b * y) ∧ ∃ a ∈ A, y * a ≠ a * y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hCB := h.symm.three_le_card_centralizer hY9 (fun y hy => (hYN y hy).2) hYodd
  have hdvd : Nat.card ↥(Y ⊓ centralizer (B : Set G)) ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Y ⊓ centralizer (B : Set G) ≤ Y)
    rw [hY9] at this
    simpa using this
  obtain ⟨k, hk, hkcard⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    rw [this, pow_zero] at hkcard
    omega
  have h3dvd : 3 ∣ Nat.card ↥(Y ⊓ centralizer (B : Set G)) := by
    rw [hkcard]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Y ⊓ centralizer (B : Set G))) 3 h3dvd
  have hy₀3 : orderOf (y₀ : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hy₀
  refine ⟨y₀, y₀.2.1, hy₀3, fun b hb => ?_, ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp y₀.2.2 b hb).symm
  · by_contra hcon
    push Not at hcon
    have hQc : A ⊔ B ≤ centralizer ({(y₀ : G)} : Set G) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcon a ha).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp y₀.2.2 b hb)
    have h1 : (y₀ : G) = 1 :=
      hY1 _ y₀.2.1 fun q hq => Subgroup.mem_centralizer_singleton_iff.mp (hQc hq)
    rw [h1, orderOf_one] at hy₀3
    omega

theorem exists_pair (h : Cfg A B) {Y : Subgroup G} (hY9 : Nat.card Y = 9)
    (hYN : ∀ y ∈ Y, y ∈ normalizer (A : Set G) ∧ y ∈ normalizer (B : Set G))
    (hYodd : ∀ y ∈ Y, Odd (orderOf y))
    (hY1 : ∀ y ∈ Y, (∀ q ∈ A ⊔ B, q * y = y * q) → y = 1) :
    ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, orderOf y₁ = 3 ∧ orderOf y₂ = 3 ∧ (∀ b ∈ B, y₁ * b = b * y₁) ∧
      (∀ a ∈ A, y₂ * a = a * y₂) ∧ (∃ a ∈ A, y₁ * a ≠ a * y₁) ∧ (∃ b ∈ B, y₂ * b ≠ b * y₂) ∧
      y₁ * y₂ = y₂ * y₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y₁, hy₁Y, hy₁3, hy₁B, hy₁A⟩ := h.exists_one hY9 hYN hYodd hY1
  obtain ⟨y₂, hy₂Y, hy₂3, hy₂A, hy₂B⟩ := h.symm.exists_one hY9
    (fun y hy => ⟨(hYN y hy).2, (hYN y hy).1⟩) hYodd
    (fun y hy hq => hY1 y hy fun q hq' => hq q (by rwa [sup_comm]))
  refine ⟨y₁, hy₁Y, y₂, hy₂Y, hy₁3, hy₂3, hy₁B, hy₂A, hy₁A, hy₂B, ?_⟩
  let hcomm : CommGroup ↥Y := IsPGroup.commGroupOfCardEqPrimeSq (p := 3) hY9
  have := mul_comm (⟨y₁, hy₁Y⟩ : Y) ⟨y₂, hy₂Y⟩
  exact congrArg Subtype.val this

end Cfg

end CFSG.Quasithin.H13.Q8SqE9

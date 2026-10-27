module

public import CFSG.Sporadic.Recognition.JankoWongKleinOrder

public section

namespace CFSG.Sporadic.Recognition.JankoWong

namespace KleinOrder

section Abelian

variable {B : Type*} [CommGroup B]

theorem mul_map_mem_fixedSub {σ : B →* B} (hσ : ∀ b, σ (σ b) = b) (y : B) :
    y * σ y ∈ fixedSub σ := by
  rw [mem_fixedSub, map_mul, hσ, mul_comm]

theorem sup_fixedSub_eq_top_of_commGroup [Finite B] (hodd : Odd (Nat.card B))
    {σ₁ σ₂ σ₃ : B →* B} (h₁ : ∀ b, σ₁ (σ₁ b) = b) (h₂ : ∀ b, σ₂ (σ₂ b) = b)
    (hc : ∀ b, σ₁ (σ₂ b) = σ₂ (σ₁ b)) (h₃ : ∀ b, σ₃ b = σ₁ (σ₂ b)) :
    fixedSub σ₁ ⊔ fixedSub σ₂ ⊔ fixedSub σ₃ = ⊤ := by
  have hσ₃ := involutive_of_prod h₁ h₂ hc h₃
  rw [eq_top_iff]
  intro y _
  obtain ⟨k, hk⟩ := hodd
  have hy : y ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_card_eq_one'
  have m₁ : y * σ₁ y ∈ fixedSub σ₁ := mul_map_mem_fixedSub h₁ y
  have m₂ : y * σ₂ y ∈ fixedSub σ₂ := mul_map_mem_fixedSub h₂ y
  have m₃ : y * σ₃ y ∈ fixedSub σ₃ := mul_map_mem_fixedSub hσ₃ y
  have mt : y * σ₁ y * σ₂ y * σ₃ y ∈ fixedSub σ₁ := by
    show σ₁ (y * σ₁ y * σ₂ y * σ₃ y) = y * σ₁ y * σ₂ y * σ₃ y
    have e₁ : σ₁ (σ₂ y) = σ₃ y := (h₃ y).symm
    have e₂ : σ₁ (σ₃ y) = σ₂ y := by rw [h₃, h₁]
    rw [map_mul, map_mul, map_mul, h₁, e₁, e₂]
    ac_rfl
  have hsq : y * y ∈ fixedSub σ₁ ⊔ fixedSub σ₂ ⊔ fixedSub σ₃ := by
    have e : y * y = (y * σ₁ y) * (y * σ₂ y) * (y * σ₃ y) * (y * σ₁ y * σ₂ y * σ₃ y)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      ac_rfl
    have l₁ : fixedSub σ₁ ≤ fixedSub σ₁ ⊔ fixedSub σ₂ ⊔ fixedSub σ₃ := le_sup_left.trans le_sup_left
    have l₂ : fixedSub σ₂ ≤ fixedSub σ₁ ⊔ fixedSub σ₂ ⊔ fixedSub σ₃ :=
      le_sup_right.trans le_sup_left
    have l₃ : fixedSub σ₃ ≤ fixedSub σ₁ ⊔ fixedSub σ₂ ⊔ fixedSub σ₃ := le_sup_right
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (l₁ m₁) (l₂ m₂)) (l₃ m₃))
      (Subgroup.inv_mem _ (l₁ mt))
  have hroot : y = (y * y) ^ (k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ, hy, one_mul]
  rw [hroot]
  exact Subgroup.pow_mem _ hsq _

theorem pow_eq_one_of_commGroup [Finite B] (hodd : Odd (Nat.card B))
    {σ₁ σ₂ σ₃ : B →* B} (h₁ : ∀ b, σ₁ (σ₁ b) = b) (h₂ : ∀ b, σ₂ (σ₂ b) = b)
    (hc : ∀ b, σ₁ (σ₂ b) = σ₂ (σ₁ b)) (h₃ : ∀ b, σ₃ b = σ₁ (σ₂ b)) (n : ℕ)
    (hn₁ : ∀ b ∈ fixedSub σ₁, b ^ n = 1) (hn₂ : ∀ b ∈ fixedSub σ₂, b ^ n = 1)
    (hn₃ : ∀ b ∈ fixedSub σ₃, b ^ n = 1) : ∀ b : B, b ^ n = 1 := by
  have hle : fixedSub σ₁ ⊔ fixedSub σ₂ ⊔ fixedSub σ₃ ≤ (powMonoidHom n : B →* B).ker :=
    sup_le (sup_le (fun b hb => hn₁ b hb) (fun b hb => hn₂ b hb)) (fun b hb => hn₃ b hb)
  rw [sup_fixedSub_eq_top_of_commGroup hodd h₁ h₂ hc h₃] at hle
  intro b
  exact hle (Subgroup.mem_top b)

end Abelian

section Conj

variable {C : Type*} [Group C]

theorem map_subtype_fixedSub_conjEnd (A : Subgroup C) (u : C) (h : ∀ y ∈ A, u * y * u⁻¹ ∈ A) :
    (fixedSub (conjEnd A u h)).map A.subtype = A ⊓ Subgroup.centralizer ({u} : Set C) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr (conjEnd_eq_self_iff.mp hy)⟩
  · rintro ⟨hxA, hxc⟩
    exact ⟨⟨x, hxA⟩,
      conjEnd_eq_self_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hxc), rfl⟩

theorem mem_inf_centralizer_of_mem_fixedSub {A : Subgroup C} {u : C}
    {h : ∀ y ∈ A, u * y * u⁻¹ ∈ A} {b : A} (hb : b ∈ fixedSub (conjEnd A u h)) :
    (b : C) ∈ A ⊓ Subgroup.centralizer ({u} : Set C) := by
  rw [← map_subtype_fixedSub_conjEnd A u h]
  exact Subgroup.mem_map_of_mem _ hb

theorem odd_card_of_isPGroup {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {G : Type*} [Group G]
    [Finite G] (hG : IsPGroup p G) : Odd (Nat.card G) := by
  obtain ⟨m, hm⟩ := hG.exists_card_eq
  rw [hm]
  exact ((Fact.out : p.Prime).odd_of_ne_two hp).pow

end Conj

end KleinOrder

open KleinOrder

variable {C : Type*} [Group C] [Finite C]

open scoped IsMulCommutative in
theorem sup_centralizers_eq_of_klein_comm_of_odd {A : Subgroup C} (hodd : Odd (Nat.card A))
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) :
    A = (A ⊓ Subgroup.centralizer ({u₁} : Set C)) ⊔ (A ⊓ Subgroup.centralizer ({u₂} : Set C)) ⊔
      (A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C)) := by
  have h₃ := conj_mul_mem h₁ h₂
  have : IsMulCommutative ↥A := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have key := sup_fixedSub_eq_top_of_commGroup (B := ↥A) hodd (σ₁ := conjEnd A u₁ h₁)
    (σ₂ := conjEnd A u₂ h₂) (σ₃ := conjEnd A (u₁ * u₂) h₃) (conjEnd_involutive hu₁ h₁)
    (conjEnd_involutive hu₂ h₂) (conjEnd_comm hc h₁ h₂) (conjEnd_mul h₁ h₂ h₃)
  have := congrArg (Subgroup.map A.subtype) key
  rw [Subgroup.map_sup, Subgroup.map_sup, map_subtype_fixedSub_conjEnd,
    map_subtype_fixedSub_conjEnd, map_subtype_fixedSub_conjEnd, Subgroup.map_top,
    Subgroup.range_subtype] at this
  exact this.symm

theorem sup_centralizers_eq_of_klein_comm {A : Subgroup C} (hA : IsPGroup 3 A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) :
    A = (A ⊓ Subgroup.centralizer ({u₁} : Set C)) ⊔ (A ⊓ Subgroup.centralizer ({u₂} : Set C)) ⊔
      (A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  sup_centralizers_eq_of_klein_comm_of_odd (odd_card_of_isPGroup (by norm_num) hA) hcomm hu₁ hu₂
    hc h₁ h₂

open scoped IsMulCommutative in
theorem pow_eq_one_of_klein_comm_of_odd {A : Subgroup C} (hodd : Odd (Nat.card A))
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A) (n : ℕ)
    (hn₁ : ∀ y ∈ A ⊓ Subgroup.centralizer ({u₁} : Set C), y ^ n = 1)
    (hn₂ : ∀ y ∈ A ⊓ Subgroup.centralizer ({u₂} : Set C), y ^ n = 1)
    (hn₃ : ∀ y ∈ A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C), y ^ n = 1) :
    ∀ y ∈ A, y ^ n = 1 := by
  have h₃ := conj_mul_mem h₁ h₂
  have : IsMulCommutative ↥A := ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have key := pow_eq_one_of_commGroup (B := ↥A) hodd (σ₁ := conjEnd A u₁ h₁)
    (σ₂ := conjEnd A u₂ h₂) (σ₃ := conjEnd A (u₁ * u₂) h₃) (conjEnd_involutive hu₁ h₁)
    (conjEnd_involutive hu₂ h₂) (conjEnd_comm hc h₁ h₂) (conjEnd_mul h₁ h₂ h₃) n
    (fun b hb => Subtype.ext (hn₁ b (mem_inf_centralizer_of_mem_fixedSub hb)))
    (fun b hb => Subtype.ext (hn₂ b (mem_inf_centralizer_of_mem_fixedSub hb)))
    (fun b hb => Subtype.ext (hn₃ b (mem_inf_centralizer_of_mem_fixedSub hb)))
  intro y hy
  exact congrArg Subtype.val (key ⟨y, hy⟩)

theorem pow_three_eq_one_of_klein_comm {A : Subgroup C} (hA : IsPGroup 3 A)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {u₁ u₂ : C} (hu₁ : u₁ ^ 2 = 1) (hu₂ : u₂ ^ 2 = 1)
    (hc : u₁ * u₂ = u₂ * u₁) (h₁ : ∀ y ∈ A, u₁ * y * u₁⁻¹ ∈ A)
    (h₂ : ∀ y ∈ A, u₂ * y * u₂⁻¹ ∈ A)
    (hn₁ : ∀ y ∈ A ⊓ Subgroup.centralizer ({u₁} : Set C), y ^ 3 = 1)
    (hn₂ : ∀ y ∈ A ⊓ Subgroup.centralizer ({u₂} : Set C), y ^ 3 = 1)
    (hn₃ : ∀ y ∈ A ⊓ Subgroup.centralizer ({u₁ * u₂} : Set C), y ^ 3 = 1) :
    ∀ y ∈ A, y ^ 3 = 1 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  pow_eq_one_of_klein_comm_of_odd (odd_card_of_isPGroup (by norm_num) hA) hcomm hu₁ hu₂ hc h₁ h₂
    3 hn₁ hn₂ hn₃

end CFSG.Sporadic.Recognition.JankoWong

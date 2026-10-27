module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenCore

public section

namespace CFSG.Sporadic.J4Schreier

open CFSG.ComponentClassification.UnbalancedCatalog

variable {M : Type*} [Group M]

theorem commute_of_inf_eq_bot' {K₁ K₂ : Subgroup M}
    (h₁ : ∀ x ∈ K₂, ∀ y ∈ K₁, x * y * x⁻¹ ∈ K₁) (h₂ : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y * x⁻¹ ∈ K₂)
    (hbot : K₁ ⊓ K₂ = ⊥) {a b : M} (ha : a ∈ K₁) (hb : b ∈ K₂) : a * b = b * a := by
  have hc₂ : a * b * a⁻¹ * b⁻¹ ∈ K₂ := mul_mem (h₂ a ha b hb) (inv_mem hb)
  have hc₁ : a * b * a⁻¹ * b⁻¹ ∈ K₁ := by
    have h := mul_mem ha (h₁ b hb a⁻¹ (inv_mem ha))
    rwa [show a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ by group] at h
  have hc : a * b * a⁻¹ * b⁻¹ ∈ K₁ ⊓ K₂ := ⟨hc₁, hc₂⟩
  rw [hbot, Subgroup.mem_bot] at hc
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hc, one_mul]

theorem eq_one_of_mem_oddCore_of_two_pow' {G : Type*} [Group G] [Finite G] {x : G}
    (hx : x ∈ CFSG.oddCore G) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card (CFSG.oddCore G) := Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (CFSG.oddCore G)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr EvenCatalog.odd_card_oddCore)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)

abbrev oddCoreImage (X : Subgroup M) : Subgroup M := (CFSG.oddCore ↥X).map X.subtype

theorem oddCoreImage_le (X : Subgroup M) : oddCoreImage X ≤ X := by
  rintro _ ⟨q, -, rfl⟩
  exact q.2

theorem oddCoreImage_conj (X : Subgroup M) {x : M} (hx : x ∈ X) {r : M}
    (hr : r ∈ oddCoreImage X) : x * r * x⁻¹ ∈ oddCoreImage X := by
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨⟨x, hx⟩ * q * ⟨x, hx⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (CFSG.oddCore ↥X).Normal).conj_mem q hq _

theorem odd_card_oddCoreImage [Finite M] (X : Subgroup M) : Odd (Nat.card (oddCoreImage X)) := by
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact EvenCatalog.odd_card_oddCore

theorem oddCore_eq_bot_of_oddCoreImage (X : Subgroup M) (h : oddCoreImage X = ⊥) :
    CFSG.oddCore ↥X = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h

theorem le_oddCore_of_normalized [Finite M] {Y S : Subgroup M} (hSY : S ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hodd : Odd (Nat.card S)) :
    S.subgroupOf Y ≤ CFSG.oddCore ↥Y := by
  refine EvenCatalog.le_oddCore_of_normal ⟨fun s hs y => ?_⟩ ?_
  · rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hnorm y y.2 s hs
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv]

theorem oddCore_eq_bot_of_normal [Finite M] {X N : Subgroup M} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN : CFSG.oddCore ↥N = ⊥)
    (hcent : ∀ x ∈ X, (∀ n ∈ N, x * n = n * x) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    CFSG.oddCore ↥X = ⊥ := by
  set R := oddCoreImage X with hRdef
  have hRN : R ⊓ N = ⊥ := by
    have hle := le_oddCore_of_normalized (Y := N) (S := R ⊓ N) inf_le_right
      (fun y hy s hs => ⟨oddCoreImage_conj X (hNX hy) hs.1, hnorm y (hNX hy) s hs.2⟩)
      (Odd.of_dvd_nat (odd_card_oddCoreImage X) (Subgroup.card_dvd_of_le inf_le_left))
    rw [hN, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : N) ∈ (R ⊓ N).subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    rw [hle, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  apply oddCore_eq_bot_of_oddCoreImage
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hrX := oddCoreImage_le X hr
  obtain ⟨k, hk⟩ := hcent r hrX fun n hn =>
    commute_of_inf_eq_bot' (fun x hx y hy => oddCoreImage_conj X (hNX hx) hy)
      (fun x hx y hy => hnorm x (oddCoreImage_le X hx) y hy) hRN hr hn
  obtain ⟨q, hq, rfl⟩ := hr
  have := eq_one_of_mem_oddCore_of_two_pow' hq (k := k) (Subtype.ext (by simpa using hk))
  rw [this]
  rfl

end CFSG.Sporadic.J4Schreier

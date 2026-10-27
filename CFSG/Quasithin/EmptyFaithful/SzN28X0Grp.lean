module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Digits.Defs

public section

namespace CFSG.Quasithin.SzN28

open Equiv
open scoped Pointwise

@[expose] def sg : Fin 7 → Perm (Fin 8) :=
  ![swap 0 1, swap 2 3, swap 4 5, swap 6 7, swap 0 2 * swap 1 3, swap 4 6 * swap 5 7,
    swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7]

@[expose] def p8Elt (a : Fin 7 → Fin 2) : Perm (Fin 8) :=
  (if a 0 = 1 then sg 0 else 1) * (if a 1 = 1 then sg 1 else 1) * (if a 2 = 1 then sg 2 else 1) *
    (if a 3 = 1 then sg 3 else 1) * (if a 4 = 1 then sg 4 else 1) * (if a 5 = 1 then sg 5 else 1) *
    (if a 6 = 1 then sg 6 else 1)

@[expose] def p8Center : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

@[expose] def code (σ : Perm (Fin 8)) : ℕ := Nat.ofDigits 8 (List.ofFn fun x : Fin 8 => (σ x : ℕ))

theorem code_injective : Function.Injective code := by
  intro σ τ h
  have h1 := Nat.ofDigits_inj_of_len_eq (by norm_num : 1 < 8) (by simp)
    (fun l hl => by
      obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hl
      exact (σ x).2) (fun l hl => by
      obtain ⟨x, rfl⟩ := List.mem_ofFn.mp hl
      exact (τ x).2) h
  have h2 : (fun x : Fin 8 => (σ x : ℕ)) = fun x => (τ x : ℕ) := List.ofFn_injective h1
  ext x
  exact congrFun h2 x

@[expose] def p8Codes : Finset ℕ := Finset.univ.image fun a => code (p8Elt a)

theorem p8Codes_card : p8Codes.card = 128 := by decide +kernel

theorem p8Codes_closed :
    ∀ i : Fin 7, ∀ a : Fin 7 → Fin 2, code (sg i * p8Elt a) ∈ p8Codes := by decide +kernel

theorem p8Codes_center : ∀ a : Fin 7 → Fin 2,
    (∀ i : Fin 7, code (p8Elt a * sg i) = code (sg i * p8Elt a)) →
      code (p8Elt a) = code 1 ∨ code (p8Elt a) = code p8Center := by decide +kernel

theorem sg_sq : ∀ i : Fin 7, sg i * sg i = 1 := by decide +kernel

@[expose] def p8 : Subgroup (Perm (Fin 8)) := Subgroup.closure (Set.range sg)

theorem p8Elt_mem (a : Fin 7 → Fin 2) : p8Elt a ∈ p8 := by
  have h : ∀ i : Fin 7, ∀ b : Fin 2, (if b = 1 then sg i else 1) ∈ p8 := fun i b => by
    by_cases hb : b = 1
    · simp only [hb, ↓reduceIte]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · simp only [hb, ↓reduceIte]
      exact p8.one_mem
  unfold p8Elt
  exact p8.mul_mem (p8.mul_mem (p8.mul_mem (p8.mul_mem (p8.mul_mem (p8.mul_mem (h 0 _) (h 1 _))
    (h 2 _)) (h 3 _)) (h 4 _)) (h 5 _)) (h 6 _)

theorem code_mem_of_mem_p8 {σ : Perm (Fin 8)} (hσ : σ ∈ p8) : code σ ∈ p8Codes := by
  induction hσ using Subgroup.closure_induction_left with
  | one => exact Finset.mem_image.2 ⟨fun _ => 0, Finset.mem_univ _, by
      have : p8Elt (fun _ => 0) = 1 := by decide +kernel
      rw [this]⟩
  | mul_left x hx y hy ih =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 ih
    have : y = p8Elt a := code_injective ha.symm
    rw [this]
    exact p8Codes_closed i a
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 ih
    have : y = p8Elt a := code_injective ha.symm
    have hinv : (sg i)⁻¹ = sg i := inv_eq_of_mul_eq_one_right (sg_sq i)
    rw [this, hinv]
    exact p8Codes_closed i a

theorem mem_p8_iff {σ : Perm (Fin 8)} : σ ∈ p8 ↔ code σ ∈ p8Codes := by
  refine ⟨code_mem_of_mem_p8, fun h => ?_⟩
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
  rw [← code_injective ha]
  exact p8Elt_mem a

theorem card_p8 : Nat.card p8 = 128 := by
  have e : p8 ≃ p8Codes :=
    Equiv.ofBijective (fun σ => ⟨code σ, mem_p8_iff.1 σ.2⟩) ⟨fun σ τ h =>
      Subtype.ext (code_injective (congrArg Subtype.val h)), fun ⟨n, hn⟩ => by
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hn
      exact ⟨⟨p8Elt a, p8Elt_mem a⟩, Subtype.ext ha⟩⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, p8Codes_card]

theorem isPGroup_p8 : IsPGroup 2 p8 := IsPGroup.of_card (n := 7) (by rw [card_p8]; norm_num)

theorem index_p8 : p8.index = 315 := by
  have h := Subgroup.card_mul_index p8
  rw [card_p8, Nat.card_perm, Nat.card_fin] at h
  have : (8 : ℕ).factorial = 40320 := by decide
  rw [this] at h
  omega

theorem center_p8 {σ : Perm (Fin 8)} (hσ : σ ∈ p8) (hc : ∀ s ∈ p8, σ * s = s * σ) :
    σ = 1 ∨ σ = p8Center := by
  obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (mem_p8_iff.1 hσ)
  have hσa : σ = p8Elt a := code_injective ha.symm
  have hgen : ∀ i : Fin 7, code (p8Elt a * sg i) = code (sg i * p8Elt a) := fun i => by
    rw [← hσa]
    exact congrArg code (hc _ (Subgroup.subset_closure ⟨i, rfl⟩))
  rcases p8Codes_center a hgen with h | h
  · exact Or.inl (by rw [hσa]; exact code_injective h)
  · exact Or.inr (by rw [hσa]; exact code_injective h)

theorem center_sylow_two_perm8 {S : Subgroup (Perm (Fin 8))} (hS : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.index) {z₁ z₂ : Perm (Fin 8)} (hz₁ : z₁ ∈ S) (hz₂ : z₂ ∈ S)
    (hc₁ : ∀ s ∈ S, z₁ * s = s * z₁) (hc₂ : ∀ s ∈ S, z₂ * s = s * z₂) :
    z₁ = 1 ∨ z₂ = 1 ∨ z₁ = z₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PS : Sylow 2 (Perm (Fin 8)) := isPGroup_p8.toSylow (by rw [index_p8]; decide)
  let SS : Sylow 2 (Perm (Fin 8)) := hS.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 8)) PS SS
  have h1 : MulAut.conj g • p8 = S := by
    have h0 : ((g • PS : Sylow 2 (Perm (Fin 8))) : Subgroup (Perm (Fin 8))) = S := by
      rw [hg]
      rfl
    rw [Sylow.coe_subgroup_smul] at h0
    exact h0
  have hgS : ∀ σ : Perm (Fin 8), σ ∈ S ↔ g⁻¹ * σ * g ∈ p8 := by
    intro σ
    rw [← h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def]
    have : (MulAut.conj g)⁻¹ σ = g⁻¹ * σ * g := by
      rw [← map_inv MulAut.conj g]
      simp
    rw [this]
  have key : ∀ z : Perm (Fin 8), z ∈ S → (∀ s ∈ S, z * s = s * z) →
      g⁻¹ * z * g = 1 ∨ g⁻¹ * z * g = p8Center := by
    intro z hz hc
    refine center_p8 ((hgS z).1 hz) fun s hs => ?_
    have hs' : g * s * g⁻¹ ∈ S := by
      rw [hgS]
      simpa [mul_assoc] using hs
    have := hc _ hs'
    calc g⁻¹ * z * g * s = g⁻¹ * (z * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * z) * g := by rw [this]
      _ = s * (g⁻¹ * z * g) := by group
  have hone : ∀ z : Perm (Fin 8), g⁻¹ * z * g = 1 → z = 1 := fun z h => by
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h]; group
  rcases key z₁ hz₁ hc₁ with h₁ | h₁
  · exact Or.inl (hone _ h₁)
  · rcases key z₂ hz₂ hc₂ with h₂ | h₂
    · exact Or.inr (Or.inl (hone _ h₂))
    · right; right
      have : g⁻¹ * z₁ * g = g⁻¹ * z₂ * g := h₁.trans h₂.symm
      exact mul_left_cancel (mul_right_cancel this)

end CFSG.Quasithin.SzN28

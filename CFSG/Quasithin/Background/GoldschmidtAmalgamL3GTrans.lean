module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Basic
public import CFSG.Quasithin.Recognition.F112WKernel

public section

namespace CFSG.Quasithin

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] {A B : Subgroup D}

theorem exists_pow_mul_mem (hidx : (A ⊓ B).relIndex A = 3) {y : D} (hy : y ∈ A)
    (hy3 : orderOf y = 3) (hyB : y ∉ B) {g : D} (hg : g ∈ A) :
    ∃ k : ℕ, k < 3 ∧ (y ^ k)⁻¹ * g ∈ B := by
  have hy2 : y ^ 2 ∉ B := fun h2 => hyB (by
    have h4 : y = (y ^ 2) ^ 2 := by
      have : y ^ 3 = 1 := hy3 ▸ pow_orderOf_eq_one y
      calc y = y ^ 3 * y := by rw [this, one_mul]
        _ = (y ^ 2) ^ 2 := by group
    rw [h4]
    exact B.pow_mem h2 2)
  have hy1 : y⁻¹ ∉ B := fun h => hyB (by simpa using B.inv_mem h)
  have hyy : y ^ 2 * y⁻¹ = y := by group
  have hidx' : Nat.card (↥A ⧸ (A ⊓ B).subgroupOf A) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have : Finite (↥A ⧸ (A ⊓ B).subgroupOf A) :=
    Nat.finite_of_card_ne_zero (by omega)
  let Y : ↥A := ⟨y, hy⟩
  let f : Fin 3 → ↥A ⧸ (A ⊓ B).subgroupOf A := fun k => ((Y ^ (k : ℕ) : ↥A) : _)
  have hmem : ∀ i j : ℕ, (↑(Y ^ i) : ↥A ⧸ (A ⊓ B).subgroupOf A) = ↑(Y ^ j) →
      (y ^ i)⁻¹ * y ^ j ∈ B := by
    intro i j hij
    have := QuotientGroup.eq.mp hij
    rw [Subgroup.mem_subgroupOf] at this
    exact (Subgroup.mem_inf.mp (by simpa using this)).2
  have hinj : Function.Injective f := by
    intro i j hij
    have h := hmem i j hij
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> first
      | exact absurd h hyB | exact absurd h hy2 | exact absurd h hy1
      | (rw [show y⁻¹ * y ^ 2 = y by group] at h; exact absurd h hyB)
      | (rw [show (y ^ 2)⁻¹ * y = y⁻¹ by group] at h; exact absurd h hy1)
  have hbij := hinj.bijective_of_nat_card_le (by rw [hidx']; simp)
  obtain ⟨k, hk⟩ := hbij.2 ((⟨g, hg⟩ : ↥A) : ↥A ⧸ (A ⊓ B).subgroupOf A)
  refine ⟨k, k.2, ?_⟩
  have := QuotientGroup.eq.mp hk
  rw [Subgroup.mem_subgroupOf] at this
  exact (Subgroup.mem_inf.mp (by simpa using this)).2

namespace GoldHyp

variable [Finite D]

theorem eq_bot_of_normalizer_transitive (h : GoldHyp A B) {U : Subgroup D} (hU : U ≤ A ⊓ B)
    (hA : ∀ g ∈ A, ∃ n ∈ A ⊓ Subgroup.normalizer (U : Set D), n⁻¹ * g ∈ B)
    (hB : ∀ g ∈ B, ∃ n ∈ B ⊓ Subgroup.normalizer (U : Set D), n⁻¹ * g ∈ A) : U = ⊥ :=
  F112W.eq_bot_of_normalizer_transitive h.amalgamHyp hU hA hB

theorem eq_bot_of_normalizes_order_three (h : GoldHyp A B) {U : Subgroup D} (hU : U ≤ A ⊓ B)
    {x y : D} (hx : x ∈ B) (hy : y ∈ A) (hx3 : orderOf x = 3) (hy3 : orderOf y = 3)
    (hxA : x ∉ A) (hyB : y ∉ B) (hxU : x ∈ Subgroup.normalizer (U : Set D))
    (hyU : y ∈ Subgroup.normalizer (U : Set D)) : U = ⊥ := by
  refine h.eq_bot_of_normalizer_transitive hU (fun g hg => ?_) (fun g hg => ?_)
  · obtain ⟨k, -, hk⟩ := exists_pow_mul_mem h.relIndex_left hy hy3 hyB hg
    exact ⟨y ^ k, ⟨A.pow_mem hy k, (Subgroup.normalizer _).pow_mem hyU k⟩, hk⟩
  · obtain ⟨k, -, hk⟩ := exists_pow_mul_mem h.symm.relIndex_left hx hx3 hxA hg
    exact ⟨x ^ k, ⟨B.pow_mem hx k, (Subgroup.normalizer _).pow_mem hxU k⟩, hk⟩

end GoldHyp

end GoldAmL

end F6

end CFSG.Quasithin

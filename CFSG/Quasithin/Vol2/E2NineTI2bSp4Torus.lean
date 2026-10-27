module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots

public section

namespace CFSG.Quasithin.E2.TI2b.Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)

variable {k : Type} [Field k] [CharP k 2]

@[expose] def ddMat (x y : kˣ) : Matrix (Fin 4) (Fin 4) k :=
  Matrix.diagonal ![(x : k), (y : k), ((y⁻¹ : kˣ) : k), ((x⁻¹ : kˣ) : k)]

omit [CharP k 2] in
theorem ddMat_mul_inv (x y : kˣ) : ddMat x y * ddMat x⁻¹ y⁻¹ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ddMat, Matrix.mul_apply, Fin.sum_univ_four]

omit [CharP k 2] in
theorem ddMat_inv_mul (x y : kˣ) : ddMat x⁻¹ y⁻¹ * ddMat x y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ddMat, Matrix.mul_apply, Fin.sum_univ_four]

omit [CharP k 2] in
theorem ddMat_mem (x y : kˣ) : (ddMat x y)ᵀ * minorJ k * ddMat x y = minorJ k := by
  ext i j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases i <;> fin_cases j <;> simp [ddMat]

omit [CharP k 2] in
private theorem ddMat_mul_uMat (x y : kˣ) (a b c d : k) :
    ddMat x y * uMat a b c d =
      uMat ((x : k) * ((y⁻¹ : kˣ) : k) * a) ((x : k) * y * b) ((x : k) ^ 2 * c)
        ((y : k) ^ 2 * d) * ddMat x y := by
  have hx : (x : k) * (x : k)⁻¹ = 1 := mul_inv_cancel₀ x.ne_zero
  have hy : (y : k) * (y : k)⁻¹ = 1 := mul_inv_cancel₀ y.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ddMat, uMat, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals first
    | ring1
    | linear_combination (-((x : k) * a)) * hy
    | linear_combination (-((x : k) * b)) * hy
    | linear_combination (-((x : k) * c)) * hx
    | linear_combination (-((y : k) * d)) * hy
    | linear_combination (-((y : k) * b) - (y : k) * a * d) * hx +
        (-((x : k) * (x : k)⁻¹ * (y : k) * a * d)) * hy
    | linear_combination (-((y : k)⁻¹ * a)) * hx

@[expose] noncomputable def dd (x y : kˣ) : antiSp k :=
  ⟨⟨ddMat x y, ddMat x⁻¹ y⁻¹, ddMat_mul_inv x y, ddMat_inv_mul x y⟩, ddMat_mem x y⟩

theorem glMat_dd (x y : kˣ) : glMat ((dd x y : antiSp k) : GL (Fin 4) k) = ddMat x y := rfl

theorem dd_conj_uElt (x y : kˣ) (a b c d : k) :
    dd x y * uElt a b c d * (dd x y)⁻¹ =
      uElt ((x : k) * ((y⁻¹ : kˣ) : k) * a) ((x : k) * y * b) ((x : k) ^ 2 * c)
        ((y : k) ^ 2 * d) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply antiSp_ext
  exact ddMat_mul_uMat x y a b c d

private theorem dd_inv (x y : kˣ) : (dd x y)⁻¹ = dd x⁻¹ y⁻¹ :=
  antiSp_ext rfl

theorem dd_mem_normalizer (x y : kˣ) :
    dd x y ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    obtain ⟨a, b, c, d, rfl⟩ := hn
    rw [dd_conj_uElt]
    exact uElt_mem_antiUnipotent _ _ _ _
  · intro hn
    obtain ⟨A, B, C, D, hABCD⟩ := hn
    have hn' : n = (dd x y)⁻¹ * (dd x y * n * (dd x y)⁻¹) * (dd x y)⁻¹⁻¹ := by group
    rw [hABCD, dd_inv] at hn'
    rw [hn', dd_conj_uElt]
    exact uElt_mem_antiUnipotent _ _ _ _

private theorem dd_conj_center (x y : kˣ) (β γ : k) :
    dd x y * uElt 0 β γ 0 * (dd x y)⁻¹ = uElt 0 ((x : k) * y * β) ((x : k) ^ 2 * γ) 0 := by
  rw [dd_conj_uElt]
  simp only [mul_zero]

private theorem dd_conj_short (x y : kˣ) (b : k) :
    dd x y * uElt 0 b 0 0 * (dd x y)⁻¹ = uElt 0 ((x : k) * y * b) 0 0 := by
  rw [dd_conj_uElt]
  simp only [mul_zero]

private theorem dd_conj_center_inv (x : kˣ) (β γ : k) :
    dd x x⁻¹ * uElt 0 β γ 0 * (dd x x⁻¹)⁻¹ = uElt 0 β ((x : k) ^ 2 * γ) 0 := by
  rw [dd_conj_center, Units.mul_inv, one_mul]

private theorem uElt_center_mul (β γ β' γ' : k) :
    uElt 0 β γ 0 * uElt 0 β' γ' 0 = uElt 0 (β + β') (γ + γ') 0 := by
  rw [uElt_mul]
  congr 1 <;> ring

private theorem uElt_zero_eq_one' : uElt (0 : k) 0 0 0 = 1 :=
  antiSp_ext uMat_zero

omit [CharP k 2] in
private theorem exists_ne_zero_ne_one_sp4 [Finite k] (hk : 4 ≤ Nat.card k) :
    ∃ t : k, t ≠ 0 ∧ t ≠ 1 := by
  classical
  haveI := Fintype.ofFinite k
  have hcard : ({0, 1} : Finset k).card < (Finset.univ : Finset k).card := by
    have h1 : ({0, 1} : Finset k).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨t, -, ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  exact ⟨t, ht.1, ht.2⟩

private theorem rootLong_le_of_mem [Finite k] (hk : 4 ≤ Nat.card k) {W : Subgroup (antiSp k)}
    (hconj : ∀ x y : kˣ, ∀ w ∈ W, dd x y * w * (dd x y)⁻¹ ∈ W) {β γ : k}
    (hwγ : uElt 0 β γ 0 ∈ W) (hγ : γ ≠ 0) : rootLong k ≤ W := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨t, ht0, ht1⟩ := exists_ne_zero_ne_one_sp4 hk
  have hu := hconj (Units.mk0 t ht0) (Units.mk0 t ht0)⁻¹ _ hwγ
  rw [dd_conj_center_inv, Units.val_mk0] at hu
  have hprod : uElt 0 0 ((1 + t ^ 2) * γ) 0 ∈ W := by
    have hm := W.mul_mem hwγ hu
    rw [uElt_center_mul, CharTwo.add_self_eq_zero] at hm
    have e : γ + t ^ 2 * γ = (1 + t ^ 2) * γ := by ring
    rwa [e] at hm
  have hsq : (1 : k) + t ^ 2 ≠ 0 := by
    intro h
    have h1 : (1 + t) ^ 2 = 0 := by linear_combination h + t * h2
    have h3 : 1 + t = 0 := (pow_eq_zero_iff two_ne_zero).mp h1
    exact ht1 (by linear_combination h3 - h2)
  have hne : (1 + t ^ 2) * γ ≠ 0 := mul_ne_zero hsq hγ
  rintro _ ⟨c, rfl⟩
  by_cases hc : c = 0
  · subst hc
    rw [uElt_zero_eq_one']
    exact W.one_mem
  ·
    obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq k 2) (c / ((1 + t ^ 2) * γ))
    have hr0 : r ≠ 0 := by
      rintro rfl
      have h0 : c / ((1 + t ^ 2) * γ) = 0 := by rw [hr, mul_zero]
      exact div_ne_zero hc hne h0
    have hcr : r ^ 2 * ((1 + t ^ 2) * γ) = c := by
      rw [pow_two r, ← hr, div_mul_cancel₀ c hne]
    have hz := hconj (Units.mk0 r hr0) 1 _ hprod
    rw [dd_conj_center, Units.val_mk0, Units.val_one, mul_zero, hcr] at hz
    exact hz

private theorem rootShort_le_of_mem [Finite k] (hk : 4 ≤ Nat.card k) {W : Subgroup (antiSp k)}
    (hconj : ∀ x y : kˣ, ∀ w ∈ W, dd x y * w * (dd x y)⁻¹ ∈ W) {β γ : k}
    (hwβ : uElt 0 β γ 0 ∈ W) (hβ : β ≠ 0) : rootShort k ≤ W := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨y, hy0, hy1⟩ := exists_ne_zero_ne_one_sp4 hk
  have hu := hconj 1 (Units.mk0 y hy0) _ hwβ
  simp only [dd_conj_center, Units.val_one, Units.val_mk0, one_mul, one_pow] at hu
  have hm := W.mul_mem hwβ hu
  rw [uElt_center_mul, CharTwo.add_self_eq_zero] at hm
  have e : β + y * β = (1 + y) * β := by ring
  rw [e] at hm
  have hne : (1 + y) * β ≠ 0 := by
    refine mul_ne_zero ?_ hβ
    intro h
    exact hy1 (by linear_combination h - h2)
  rintro _ ⟨b, rfl⟩
  by_cases hb : b = 0
  · subst hb
    rw [uElt_zero_eq_one']
    exact W.one_mem
  ·
    have hs : b / ((1 + y) * β) ≠ 0 := div_ne_zero hb hne
    have hz := hconj (Units.mk0 (b / ((1 + y) * β)) hs) 1 _ hm
    simp only [dd_conj_short, Units.val_mk0, Units.val_one, mul_one] at hz
    rw [div_mul_cancel₀ b hne] at hz
    exact hz

theorem borelInvariant_center [Finite k] (hk : 4 ≤ Nat.card k) {W : Subgroup (antiSp k)}
    (hW : W ≤ antiUnipotentCenter k)
    (hinv : ∀ b ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)), ∀ w ∈ W,
      b * w * b⁻¹ ∈ W) :
    W = ⊥ ∨ W = rootLong k ∨ W = rootShort k ∨ W = antiUnipotentCenter k := by
  have hconj : ∀ x y : kˣ, ∀ w ∈ W, dd x y * w * (dd x y)⁻¹ ∈ W :=
    fun x y w hw => hinv (dd x y) (dd_mem_normalizer x y) w hw
  have hcoord : ∀ w ∈ W, ∃ β γ : k, w = uElt 0 β γ 0 := fun w hw => hW hw
  by_cases hL : ∃ β γ : k, uElt 0 β γ 0 ∈ W ∧ γ ≠ 0
  · obtain ⟨β₀, γ₀, hwγ, hγ⟩ := hL
    have hLW : rootLong k ≤ W := rootLong_le_of_mem hk hconj hwγ hγ
    by_cases hS : ∃ β γ : k, uElt 0 β γ 0 ∈ W ∧ β ≠ 0
    · obtain ⟨β₁, γ₁, hwβ, hβ⟩ := hS
      have hSW : rootShort k ≤ W := rootShort_le_of_mem hk hconj hwβ hβ
      right; right; right
      refine le_antisymm hW ?_
      calc antiUnipotentCenter k = rootLong k ⊔ rootShort k :=
            CFSG.Quasithin.SteinbergBS.rootLong_sup_rootShort.symm
        _ ≤ W := sup_le hLW hSW
    · right; left
      refine le_antisymm ?_ hLW
      intro w hw
      obtain ⟨β, γ, rfl⟩ := hcoord w hw
      have hβ : β = 0 := by
        by_contra h
        exact hS ⟨β, γ, hw, h⟩
      subst hβ
      exact ⟨γ, rfl⟩
  · simp only [not_exists, not_and, ne_eq, not_not] at hL
    by_cases hS : ∃ β γ : k, uElt 0 β γ 0 ∈ W ∧ β ≠ 0
    · obtain ⟨β₁, γ₁, hwβ, hβ⟩ := hS
      have hSW : rootShort k ≤ W := rootShort_le_of_mem hk hconj hwβ hβ
      right; right; left
      refine le_antisymm ?_ hSW
      intro w hw
      obtain ⟨β, γ, rfl⟩ := hcoord w hw
      have hγ : γ = 0 := hL β γ hw
      subst hγ
      exact ⟨β, rfl⟩
    · simp only [not_exists, not_and, ne_eq, not_not] at hS
      left
      rw [eq_bot_iff]
      intro w hw
      obtain ⟨β, γ, rfl⟩ := hcoord w hw
      have hβ : β = 0 := hS β γ hw
      have hγ : γ = 0 := hL β γ hw
      subst hβ
      subst hγ
      exact (Subgroup.mem_bot).mpr uElt_zero_eq_one'

end CFSG.Quasithin.E2.TI2b.Sp4

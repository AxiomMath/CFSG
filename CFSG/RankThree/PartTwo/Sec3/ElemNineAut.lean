module

import CFSG.GroupTheory.NormalOddInversion
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec3

variable {B : Type*} [CommGroup B]

theorem mulAut_apply_apply_of_mul_self {σ : MulAut B} (hσ : σ * σ = 1) (b : B) :
    σ (σ b) = b := by
  rw [← MulAut.mul_apply, hσ, MulAut.one_apply]

theorem exists_apply_eq_inv_of_mul_self_eq_one {σ : MulAut B} (hσ : σ * σ = 1)
    (hσ1 : σ ≠ 1) : ∃ d : B, d ≠ 1 ∧ σ d = d⁻¹ :=
  CFSG.GroupTheory.exists_ne_one_apply_eq_inv_of_mul_self_eq_one hσ hσ1

theorem ne_one_of_not_mem_zpowers {x y : B} (hy : y ∉ Subgroup.zpowers x) : y ≠ 1 :=
  fun h => hy (h ▸ Subgroup.one_mem _)

theorem eq_inv_of_forall {σ : MulAut B} (h : ∀ b, σ b = b⁻¹) : σ = MulEquiv.inv B :=
  MulEquiv.ext fun b => by rw [h, MulEquiv.inv_apply]

section Three

variable (h3 : ∀ b : B, b ^ 3 = 1)
include h3

theorem inv_eq_sq_of_pow_three (b : B) : b⁻¹ = b ^ 2 := by
  have := h3 b
  rw [pow_succ] at this
  exact (eq_inv_of_mul_eq_one_left this).symm

theorem pow_eq_pow_mod_three (b : B) (k : ℕ) : b ^ k = b ^ (k % 3) := by
  conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]

theorem eq_one_of_mul_self_eq_one {b : B} (hb : b * b = 1) : b = 1 := by
  have h := h3 b
  rw [pow_succ, pow_two, hb, one_mul] at h
  exact h

theorem fixed_mul_inverted {σ : MulAut B} (hσ : σ * σ = 1) (b : B) :
    σ (b * σ b)⁻¹ = (b * σ b)⁻¹ ∧ σ (σ b * b⁻¹) = (σ b * b⁻¹)⁻¹ ∧
      (b * σ b)⁻¹ * (σ b * b⁻¹) = b := by
  have h2 := mulAut_apply_apply_of_mul_self hσ b
  refine ⟨?_, ?_, ?_⟩
  · rw [map_inv, map_mul, h2, mul_comm]
  · rw [map_mul, map_inv, h2, mul_inv_rev, inv_inv]
  · have : (b * σ b)⁻¹ * (σ b * b⁻¹) = b⁻¹ * b⁻¹ := by rw [mul_inv]; group
    rw [this, inv_eq_sq_of_pow_three h3, ← pow_add, pow_eq_pow_mod_three h3]
    norm_num

theorem exists_apply_eq_self_of_mul_self_eq_one {σ : MulAut B} (hσ : σ * σ = 1)
    (hσι : ¬ ∀ b, σ b = b⁻¹) : ∃ x : B, x ≠ 1 ∧ σ x = x := by
  by_contra h
  push Not at h
  apply hσι
  intro b
  obtain ⟨h1, h2, h3'⟩ := fixed_mul_inverted h3 hσ b
  have hfix : (b * σ b)⁻¹ = 1 := by
    by_contra hne
    exact h _ hne h1
  rw [hfix, one_mul] at h3'
  rw [← h3', h2]

theorem pow_mod_three_eq_zero_of_mem_zpowers {x y : B} (hy : y ∉ Subgroup.zpowers x) {k : ℕ}
    (hk : y ^ k ∈ Subgroup.zpowers x) : k % 3 = 0 := by
  rw [pow_eq_pow_mod_three h3] at hk
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k % 3
  · rfl
  · rw [pow_one] at hk; exact absurd hk hy
  · apply absurd _ hy
    have := Subgroup.pow_mem _ hk 2
    rwa [← pow_mul, pow_eq_pow_mod_three h3, show 2 * 2 % 3 = 1 from rfl, pow_one] at this

theorem pow_mod_three_eq_zero_of_pow_eq_one {x : B} (hx : x ≠ 1) {k : ℕ} (hk : x ^ k = 1) :
    k % 3 = 0 := by
  have h : x ^ k ∈ (⊥ : Subgroup B) := by rw [hk]; exact Subgroup.one_mem _
  have hx' : x ∉ Subgroup.zpowers (1 : B) := by
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]; exact hx
  exact pow_mod_three_eq_zero_of_mem_zpowers h3 hx' (by rwa [Subgroup.zpowers_one_eq_bot])

theorem bijective_pow_mul_pow [Finite B] (h9 : Nat.card B = 9) {x y : B} (hx : x ≠ 1)
    (hy : y ∉ Subgroup.zpowers x) :
    Function.Bijective (fun p : Fin 3 × Fin 3 => x ^ (p.1 : ℕ) * y ^ (p.2 : ℕ)) := by
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only at h
    have hinv : ∀ (b : B) (k : ℕ), (b ^ k)⁻¹ = b ^ (2 * k) := fun b k => by
      rw [← inv_pow, inv_eq_sq_of_pow_three h3, ← pow_mul]
    have h1 : y ^ ((j : ℕ) + 2 * (j' : ℕ)) = x ^ ((i' : ℕ) + 2 * (i : ℕ)) := by
      rw [pow_add, pow_add, ← hinv, ← hinv]
      have : y ^ (j : ℕ) = (x ^ (i : ℕ))⁻¹ * (x ^ (i' : ℕ) * y ^ (j' : ℕ)) := by
        rw [← h, inv_mul_cancel_left]
      rw [this]
      group
    have hj : ((j : ℕ) + 2 * (j' : ℕ)) % 3 = 0 :=
      pow_mod_three_eq_zero_of_mem_zpowers h3 hy (h1 ▸ Subgroup.npow_mem_zpowers x _)
    have hjj : j = j' := by
      have := j.2; have := j'.2
      exact Fin.ext (by omega)
    subst hjj
    have h2 : x ^ ((i : ℕ) + 2 * (i' : ℕ)) = 1 := by
      rw [pow_add, ← hinv, mul_right_cancel h]
      exact mul_inv_cancel _
    have hi : ((i : ℕ) + 2 * (i' : ℕ)) % 3 = 0 := pow_mod_three_eq_zero_of_pow_eq_one h3 hx h2
    have hii : i = i' := by
      have := i.2; have := i'.2
      exact Fin.ext (by omega)
    rw [hii]
  · rw [h9, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem mulAut_ext_of_basis [Finite B] (h9 : Nat.card B = 9) {x y : B} (hx : x ≠ 1)
    (hy : y ∉ Subgroup.zpowers x) {σ τ : MulAut B} (hσx : σ x = τ x) (hσy : σ y = τ y) :
    σ = τ := by
  apply MulEquiv.ext
  intro b
  obtain ⟨⟨i, j⟩, rfl⟩ := (bijective_pow_mul_pow h3 h9 hx hy).2 b
  simp only [map_mul, map_pow, hσx, hσy]

theorem exists_not_mem_zpowers [Finite B] (h9 : Nat.card B = 9) (x : B) :
    ∃ y : B, y ∉ Subgroup.zpowers x := by
  by_contra h
  push Not at h
  have hle : Nat.card (⊤ : Subgroup B) ≤ Nat.card (Subgroup.zpowers x) :=
    Subgroup.card_le_of_le (fun y _ => h y)
  rw [Subgroup.card_top, h9, Nat.card_zpowers] at hle
  have hdvd : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (h3 x)
  have : orderOf x ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem eq_one_of_apply_eq_self_of_apply_eq_inv {σ : MulAut B} {b : B} (h1 : σ b = b)
    (h2 : σ b = b⁻¹) : b = 1 := by
  apply eq_one_of_mul_self_eq_one h3
  rw [h1] at h2
  calc b * b = b * b⁻¹ := by rw [← h2]
    _ = 1 := mul_inv_cancel b

theorem exists_eq_pow_of_apply_eq_self [Finite B] (h9 : Nat.card B = 9) {σ : MulAut B} {x y : B}
    (hx1 : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) (hσx : σ x = x) (hσy : σ y = y⁻¹) {b : B}
    (hb : σ b = b) : ∃ i : ℕ, i < 3 ∧ b = x ^ i := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (bijective_pow_mul_pow h3 h9 hx1 hy).2 b
  simp only at hb ⊢
  rw [map_mul, map_pow, map_pow, hσx, hσy, inv_pow] at hb
  have hj : (y ^ (j : ℕ)) * (y ^ (j : ℕ)) = 1 := by
    have := mul_left_cancel hb
    rw [← mul_inv_cancel (y ^ (j : ℕ))]
    congr 1
    exact this.symm
  have hj1 := eq_one_of_mul_self_eq_one h3 hj
  exact ⟨i, i.2, by rw [hj1, mul_one]⟩

theorem exists_eq_pow_of_apply_eq_inv [Finite B] (h9 : Nat.card B = 9) {σ : MulAut B} {x y : B}
    (hx1 : x ≠ 1) (hy : y ∉ Subgroup.zpowers x) (hσx : σ x = x) (hσy : σ y = y⁻¹) {b : B}
    (hb : σ b = b⁻¹) : ∃ j : ℕ, j < 3 ∧ b = y ^ j := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (bijective_pow_mul_pow h3 h9 hx1 hy).2 b
  simp only at hb ⊢
  rw [map_mul, map_pow, map_pow, hσx, hσy, inv_pow, mul_inv] at hb
  have hi : (x ^ (i : ℕ)) * (x ^ (i : ℕ)) = 1 := by
    have := mul_right_cancel hb
    rw [← mul_inv_cancel (x ^ (i : ℕ))]
    congr 1
  have hi1 := eq_one_of_mul_self_eq_one h3 hi
  exact ⟨j, j.2, by rw [hi1, one_mul]⟩

theorem inv_mem_of_commute [Finite B] (h9 : Nat.card B = 9) {σ τ : MulAut B}
    (hσ : σ * σ = 1) (hστ : σ * τ = τ * σ) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1)
    (hne : σ ≠ τ) : (∀ b, σ b = b⁻¹) ∨ (∀ b, τ b = b⁻¹) ∨ ∀ b, (σ * τ) b = b⁻¹ := by
  by_cases hσι : ∀ b, σ b = b⁻¹
  · exact Or.inl hσι
  right
  obtain ⟨x, hx1, hσx⟩ := exists_apply_eq_self_of_mul_self_eq_one h3 hσ hσι
  obtain ⟨y, hy1, hσy⟩ := exists_apply_eq_inv_of_mul_self_eq_one hσ hσ1
  have hy : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    apply hy1
    apply eq_one_of_apply_eq_self_of_apply_eq_inv h3 (σ := σ)
    · rw [map_zpow, hσx]
    · exact hσy
  have hcomm : ∀ b, σ (τ b) = τ (σ b) := fun b => by
    rw [← MulAut.mul_apply, hστ, MulAut.mul_apply]
  obtain ⟨i, hi3, hτx⟩ := exists_eq_pow_of_apply_eq_self h3 h9 hx1 hy hσx hσy
    (b := τ x) (by rw [hcomm, hσx])
  obtain ⟨j, hj3, hτy⟩ := exists_eq_pow_of_apply_eq_inv h3 h9 hx1 hy hσx hσy
    (b := τ y) (by rw [hcomm, hσy, map_inv])
  have hτx1 : τ x ≠ 1 := fun h => hx1 (by rw [← map_one τ] at h; exact τ.injective h)
  have hτy1 : τ y ≠ 1 := fun h => hy1 (by rw [← map_one τ] at h; exact τ.injective h)
  have hinvx : x⁻¹ = x ^ 2 := inv_eq_sq_of_pow_three h3 x
  have hinvy : y⁻¹ = y ^ 2 := inv_eq_sq_of_pow_three h3 y
  interval_cases i
  · exact absurd (by rw [hτx, pow_zero]) hτx1
  · interval_cases j
    · exact absurd (by rw [hτy, pow_zero]) hτy1
    · exact absurd (mulAut_ext_of_basis h3 h9 hx1 hy (σ := τ) (τ := 1)
        (by rw [hτx, pow_one, MulAut.one_apply]) (by rw [hτy, pow_one, MulAut.one_apply])) hτ1
    · exact absurd (mulAut_ext_of_basis h3 h9 hx1 hy (by rw [hτx, pow_one, hσx])
        (by rw [hτy, hσy, hinvy])).symm hne
  · interval_cases j
    · exact absurd (by rw [hτy, pow_zero]) hτy1
    ·
      right
      have heq : σ * τ = MulEquiv.inv B := mulAut_ext_of_basis h3 h9 hx1 hy
        (by rw [MulAut.mul_apply, hτx, map_pow, hσx, MulEquiv.inv_apply, hinvx])
        (by rw [MulAut.mul_apply, hτy, pow_one, hσy, MulEquiv.inv_apply])
      intro b
      rw [heq, MulEquiv.inv_apply]
    ·
      left
      have heq : τ = MulEquiv.inv B := mulAut_ext_of_basis h3 h9 hx1 hy
        (by rw [hτx, MulEquiv.inv_apply, hinvx]) (by rw [hτy, MulEquiv.inv_apply, hinvy])
      intro b
      rw [heq, MulEquiv.inv_apply]

theorem card_le_four [Finite B] (h9 : Nat.card B = 9) (E : Subgroup (MulAut B))
    (hE2 : ∀ σ ∈ E, σ * σ = 1) (hEc : ∀ σ ∈ E, ∀ τ ∈ E, σ * τ = τ * σ) : Nat.card E ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have : Finite (MulAut B) := inferInstance
  have hfin : Finite E := inferInstance
  have : Fintype E := Fintype.ofFinite E
  have hout : ∀ s : Finset E, s.card < Nat.card E → ∃ σ : E, σ ∉ s := by
    intro s hs
    by_contra h
    push Not at h
    have : Finset.univ ⊆ s := fun σ _ => h σ
    have := Finset.card_le_card this
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    omega
  obtain ⟨σ, hσ⟩ := hout {1} (by rw [Finset.card_singleton]; omega)
  obtain ⟨τ, hτ⟩ := hout {1, σ} (by
    refine lt_of_le_of_lt (Finset.card_le_two) ?_; omega)
  obtain ⟨ρ, hρ⟩ := hout {1, σ, τ, σ * τ} (by
    refine lt_of_le_of_lt (Finset.card_le_four) hlt)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ hτ hρ
  have hval : ∀ a b : E, a ≠ b → (a : MulAut B) ≠ b := fun a b h h' => h (Subtype.ext h')
  have hsq : ∀ a : E, (a : MulAut B) * a = 1 := fun a => hE2 a a.2
  have hc : ∀ a b : E, (a : MulAut B) * b = b * a := fun a b => hEc a a.2 b b.2
  have hne1 : ∀ a : E, a ≠ 1 → (a : MulAut B) ≠ 1 := fun a h h' => h (Subtype.ext h')
  have key : ∀ a b : E, a ≠ 1 → b ≠ 1 → a ≠ b →
      (a : MulAut B) = MulEquiv.inv B ∨ (b : MulAut B) = MulEquiv.inv B ∨
        (a : MulAut B) * b = MulEquiv.inv B := fun a b ha hb hab => by
    rcases inv_mem_of_commute h3 h9 (hsq a) (hc a b) (hne1 a ha) (hne1 b hb) (hval a b hab)
      with h | h | h
    · exact Or.inl (eq_inv_of_forall h)
    · exact Or.inr (Or.inl (eq_inv_of_forall h))
    · exact Or.inr (Or.inr (eq_inv_of_forall h))
  have hστ' : ρ ≠ σ * τ := hρ.2.2.2
  have hcancel : ∀ a b c : MulAut B, a * b = a * c → b = c := fun a b c h => mul_left_cancel h
  rcases key σ τ hσ (Ne.symm hτ.1 |>.symm) (Ne.symm hτ.2) with h1 | h1 | h1
  ·
    rcases key τ ρ hτ.1 hρ.1 (Ne.symm hρ.2.2.1) with h2 | h2 | h2
    · exact hτ.2 (Subtype.ext (h2.trans h1.symm))
    · exact hρ.2.1 (Subtype.ext (h2.trans h1.symm))
    · apply hστ'
      apply Subtype.ext
      rw [← h1] at h2
      rw [Subgroup.coe_mul]
      calc (ρ : MulAut B) = τ * (τ * ρ) := by rw [← mul_assoc, hsq τ, one_mul]
        _ = τ * σ := by rw [h2]
        _ = σ * τ := hc τ σ
  ·
    rcases key σ ρ hσ hρ.1 (Ne.symm hρ.2.1) with h2 | h2 | h2
    · exact hτ.2 (Subtype.ext (h1.trans h2.symm))
    · exact hρ.2.2.1 (Subtype.ext (h2.trans h1.symm))
    · apply hστ'
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      calc (ρ : MulAut B) = σ * (σ * ρ) := by rw [← mul_assoc, hsq σ, one_mul]
        _ = σ * τ := by rw [h2, h1]
  ·
    rcases key σ ρ hσ hρ.1 (Ne.symm hρ.2.1) with h2 | h2 | h2
    · apply hτ.1
      apply Subtype.ext
      rw [Subgroup.coe_one]
      have : (σ : MulAut B) * τ = σ * 1 := by rw [h1, h2, mul_one]
      exact hcancel _ _ _ this
    · exact hστ' (Subtype.ext (by rw [Subgroup.coe_mul, h1, h2]))
    · apply hρ.2.2.1
      apply Subtype.ext
      exact hcancel _ _ _ (h2.trans h1.symm)

theorem ne_inv_self_of_ne_one {y : B} (hy : y ≠ 1) : y ≠ y⁻¹ := fun h =>
  hy (eq_one_of_mul_self_eq_one h3 (by
    calc y * y = y * y⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel y))

omit h3 in
theorem eq_one_of_pow_three_of_isPGroup {R : Subgroup (MulAut B)} (hR : IsPGroup 2 R)
    {ρ : MulAut B} (hρR : ρ ∈ R) (hρ3 : ρ ^ 3 = 1) : ρ = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨ρ, hρR⟩
  have hk' : ρ ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have h1 : orderOf ρ ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hρ3) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem eq_of_apply_eq_self [Finite B] (h9 : Nat.card B = 9) {R : Subgroup (MulAut B)}
    (hR : IsPGroup 2 R) {x : B} (hx : x ≠ 1) {σ τ : MulAut B} (hσR : σ ∈ R) (hτR : τ ∈ R)
    (hσx : σ x = x) (hτx : τ x = x) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) : σ = τ := by
  obtain ⟨y, hy⟩ := exists_not_mem_zpowers h3 h9 x
  have hbij := bijective_pow_mul_pow h3 h9 hx hy
  have hunip : ∀ ρ ∈ R, ρ x = x → ∀ a : ℕ, ρ y = x ^ a * y → ρ = 1 := by
    intro ρ hρR hρx a hρy
    refine eq_one_of_pow_three_of_isPGroup hR hρR (mulAut_ext_of_basis h3 h9 hx hy ?_ ?_)
    · rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hρx, hρx, hρx, MulAut.one_apply]
    · rw [pow_three, MulAut.mul_apply, MulAut.mul_apply, hρy, map_mul, map_pow, hρx, hρy,
        map_mul, map_pow, map_mul, map_pow, hρx, hρy, MulAut.one_apply]
      have : x ^ a * (x ^ a * (x ^ a * y)) = (x ^ 3) ^ a * y := by
        rw [← pow_mul, mul_comm 3 a, pow_mul]; group
      rw [this, h3, one_pow, one_mul]
  have hform : ∀ ρ ∈ R, ρ x = x → ρ ≠ 1 → ∃ a : ℕ, ρ y = x ^ a * y ^ 2 := by
    intro ρ hρR hρx hρ1
    obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 (ρ y)
    simp only at hab
    have hb := b.2
    interval_cases hb' : (b : ℕ)
    · exfalso
      apply hy
      have : ρ y = ρ (x ^ (a : ℕ)) := by rw [← hab, pow_zero, mul_one, map_pow, hρx]
      rw [ρ.injective this]
      exact Subgroup.npow_mem_zpowers x _
    · exact absurd (hunip ρ hρR hρx a (by rw [← hab, pow_one])) hρ1
    · exact ⟨a, hab.symm⟩
  have hsq : ∀ ρ ∈ R, ρ x = x → ∀ a : ℕ, ρ y = x ^ a * y ^ 2 →
      ∀ ρ' : MulAut B, ρ' x = x → ∀ a' : ℕ, ρ' y = x ^ a' * y ^ 2 →
        ∃ c : ℕ, (ρ' * ρ) y = x ^ c * y := by
    intro ρ _ hρx a hρy ρ' hρ'x a' hρ'y
    refine ⟨a + 2 * a', ?_⟩
    rw [MulAut.mul_apply, hρy, map_mul, map_pow, map_pow, hρ'x, hρ'y, mul_pow, ← pow_mul,
      ← pow_mul, ← mul_assoc, ← pow_add, pow_eq_pow_mod_three h3 y (2 * 2),
      show 2 * 2 % 3 = 1 from rfl, pow_one, mul_comm a' 2]
  obtain ⟨a, hσy⟩ := hform σ hσR hσx hσ1
  obtain ⟨a', hτy⟩ := hform τ hτR hτx hτ1
  obtain ⟨c, hc⟩ := hsq τ hτR hτx a' hτy σ hσx a hσy
  obtain ⟨c', hc'⟩ := hsq τ hτR hτx a' hτy τ hτx a' hτy
  have h1 : σ * τ = 1 := hunip _ (R.mul_mem hσR hτR) (by rw [MulAut.mul_apply, hτx, hσx]) c hc
  have h2 : τ * τ = 1 := hunip _ (R.mul_mem hτR hτR) (by rw [MulAut.mul_apply, hτx, hτx]) c' hc'
  calc σ = σ * (τ * τ) := by rw [h2, mul_one]
    _ = τ := by rw [← mul_assoc, h1, one_mul]

theorem exists_apply_eq_of_quaternion [Finite B] (h9 : Nat.card B = 9)
    {K : Subgroup (MulAut B)} (e : K ≃* QuaternionGroup 2) {x y : B} (hx : x ≠ 1)
    (hy : y ≠ 1) : ∃ σ ∈ K, σ x = y := by
  classical
  have hq1 : ∀ q : QuaternionGroup 2, q = 1 ∨ q = QuaternionGroup.a 2 ∨
      q * q = QuaternionGroup.a 2 := by decide
  set z : MulAut B := ((e.symm (QuaternionGroup.a 2) : K) : MulAut B) with hzdef
  set h₀ : MulAut B := ((e.symm (QuaternionGroup.a 1) : K) : MulAut B) with hh₀def
  have hz1 : z ≠ 1 := by
    intro h
    have : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    rw [MulEquiv.symm_apply_eq, map_one] at this
    exact absurd this (by decide)
  have hzz : z * z = 1 := by
    rw [hzdef, ← Subgroup.coe_mul, ← map_mul,
      show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 by decide,
      map_one, Subgroup.coe_one]
  have hh₀z : h₀ * h₀ = z := by
    rw [hh₀def, hzdef, ← Subgroup.coe_mul, ← map_mul,
      show (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
        QuaternionGroup.a 2 by decide]
  have htri : ∀ k : K, (k : MulAut B) = 1 ∨ (k : MulAut B) = z ∨
      (k : MulAut B) * k = z := by
    intro k
    rcases hq1 (e k) with h | h | h
    · left
      rw [show k = 1 from e.injective (h.trans (map_one e).symm), Subgroup.coe_one]
    · right; left
      rw [hzdef, ← h, MulEquiv.symm_apply_apply]
    · right; right
      rw [hzdef, ← h, ← map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
  have hzι : ∀ b, z b = b⁻¹ := by
    by_contra hne
    obtain ⟨x₀, hx₀1, hzx₀⟩ := exists_apply_eq_self_of_mul_self_eq_one h3 hzz hne
    obtain ⟨y₀, hy₀1, hzy₀⟩ := exists_apply_eq_inv_of_mul_self_eq_one hzz hz1
    have hy₀ : y₀ ∉ Subgroup.zpowers x₀ := by
      intro hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      apply hy₀1
      apply eq_one_of_apply_eq_self_of_apply_eq_inv h3 (σ := z)
      · rw [map_zpow, hzx₀]
      · exact hzy₀
    have hcomm : ∀ b, z (h₀ b) = h₀ (z b) := fun b => by
      rw [← hh₀z, MulAut.mul_apply, MulAut.mul_apply]
    obtain ⟨j, hj3, hh₀y₀⟩ := exists_eq_pow_of_apply_eq_inv h3 h9 hx₀1 hy₀ hzx₀ hzy₀
      (b := h₀ y₀) (by rw [hcomm, hzy₀, map_inv])
    have hzy₀' : z y₀ = y₀ ^ (j * j) := by
      rw [← hh₀z, MulAut.mul_apply, hh₀y₀, map_pow, hh₀y₀, ← pow_mul]
    rw [hzy₀] at hzy₀'
    interval_cases j
    · exfalso
      apply hy₀1
      have : h₀ y₀ = h₀ 1 := by rw [hh₀y₀, pow_zero, map_one]
      exact h₀.injective this
    · exact ne_inv_self_of_ne_one h3 hy₀1 (by rw [hzy₀']; norm_num)
    · exact ne_inv_self_of_ne_one h3 hy₀1 (by
        rw [hzy₀', pow_eq_pow_mod_three h3]; norm_num)
  have hstab : ∀ k : K, (k : MulAut B) x = x → k = 1 := by
    intro k hkx
    rcases htri k with h | h | h
    · exact Subtype.ext h
    · exfalso
      rw [h, hzι] at hkx
      exact ne_inv_self_of_ne_one h3 hx hkx.symm
    · exfalso
      have : ((k : MulAut B) * k) x = x := by rw [MulAut.mul_apply, hkx, hkx]
      rw [h, hzι] at this
      exact ne_inv_self_of_ne_one h3 hx this.symm
  let f : K → {b : B // b ≠ 1} := fun k => ⟨(k : MulAut B) x, fun h => hx (by
    rw [← map_one (k : MulAut B)] at h; exact (k : MulAut B).injective h)⟩
  have hf : Function.Injective f := by
    intro k k' hkk'
    have h1 : (k : MulAut B) x = (k' : MulAut B) x := congrArg Subtype.val hkk'
    have h2 : ((k'⁻¹ * k : K) : MulAut B) x = x := by
      rw [Subgroup.coe_mul, MulAut.mul_apply, h1, Subgroup.coe_inv, ← MulAut.mul_apply,
        inv_mul_cancel, MulAut.one_apply]
    have := hstab _ h2
    rw [inv_mul_eq_one] at this
    exact this.symm
  have hcardK : Nat.card K = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardB : Nat.card {b : B // b ≠ 1} = 8 := by
    have : Fintype B := Fintype.ofFinite B
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card, h9]
  obtain ⟨k, hk⟩ := (hf.bijective_of_nat_card_le (by rw [hcardK, hcardB])).2 ⟨y, hy⟩
  exact ⟨k, k.2, congrArg Subtype.val hk⟩

theorem eq_one_or_inv_of_normal [Finite B] (h9 : Nat.card B = 9) {R F : Subgroup (MulAut B)}
    (htr : ∀ x y : B, x ≠ 1 → y ≠ 1 → ∃ r ∈ R, r x = y)
    (hFn : ∀ r ∈ R, ∀ f ∈ F, r * f * r⁻¹ ∈ F) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFc : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f) {f : MulAut B} (hf : f ∈ F) :
    f = 1 ∨ ∀ b, f b = b⁻¹ := by
  by_contra h
  push Not at h
  obtain ⟨hf1, b₀, hb₀⟩ := h
  have hfι : ¬ ∀ b, f b = b⁻¹ := fun h' => hb₀ (h' b₀)
  obtain ⟨x, hx1, hfx⟩ := exists_apply_eq_self_of_mul_self_eq_one h3 (hF2 f hf) hfι
  obtain ⟨y, hy1, hfy⟩ := exists_apply_eq_inv_of_mul_self_eq_one (hF2 f hf) hf1
  have hy : y ∉ Subgroup.zpowers x := by
    intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    apply hy1
    apply eq_one_of_apply_eq_self_of_apply_eq_inv h3 (σ := f)
    · rw [map_zpow, hfx]
    · exact hfy
  have hxy1 : x * y ≠ 1 := fun h => hy (by
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  obtain ⟨r, hrR, hrx⟩ := htr x y hx1 hy1
  obtain ⟨r', hr'R, hr'x⟩ := htr x (x * y) hx1 hxy1
  have hconj : ∀ ρ : MulAut B, ∀ v w : B, ρ v = w → (ρ * f * ρ⁻¹) w = ρ (f v) := by
    intro ρ v w hv
    rw [← hv, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hf'y : (r * f * r⁻¹) y = y := by rw [hconj r x y hrx, hfx, hrx]
  have hf''y : (r' * f * r'⁻¹) (x * y) = x * y := by rw [hconj r' x (x * y) hr'x, hfx, hr'x]
  have hne_one : ∀ ρ : MulAut B, ρ * f * ρ⁻¹ ≠ 1 := fun ρ h => hf1 (by
    have h' : ρ * f = ρ := mul_inv_eq_one.mp h
    calc f = ρ⁻¹ * (ρ * f) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = 1 := by rw [h', inv_mul_cancel])
  have key : ∀ g ∈ F, g ≠ 1 → g ≠ f → (¬ ∀ b, g b = b⁻¹) → g = f * MulEquiv.inv B := by
    intro g hgF hg1 hgf hgι
    rcases inv_mem_of_commute h3 h9 (hF2 f hf) (hFc f hf g hgF) hf1 hg1 (Ne.symm hgf) with
      h | h | h
    · exact absurd h hfι
    · exact absurd h hgι
    · have := eq_inv_of_forall h
      calc g = f * (f * g) := by rw [← mul_assoc, hF2 f hf, one_mul]
        _ = f * MulEquiv.inv B := by rw [this]
  have hyinv := ne_inv_self_of_ne_one h3 hy1
  have hxyinv := ne_inv_self_of_ne_one h3 hxy1
  have h1 := key _ (hFn r hrR f hf) (hne_one r)
    (fun h => hyinv (by rw [← hfy, ← h, hf'y]))
    (fun h => hyinv (by rw [← h y, hf'y]))
  have h2 := key _ (hFn r' hr'R f hf) (hne_one r')
    (fun h => hyinv (by
      have := hf''y
      rw [h, map_mul, hfx, hfy] at this
      exact (mul_left_cancel this).symm))
    (fun h => hxyinv (by rw [← h (x * y), hf''y]))
  have h3' : (r * f * r⁻¹) (x * y) = x * y := by rw [h1, ← h2, hf''y]
  rw [h1, MulAut.mul_apply, MulEquiv.inv_apply, map_inv, map_mul, hfx, hfy, mul_inv,
    inv_inv] at h3'
  have : x⁻¹ = x := mul_right_cancel h3'
  exact ne_inv_self_of_ne_one h3 hx1 this.symm

end Three

end CFSG.RankThree.PartTwo.Sec3

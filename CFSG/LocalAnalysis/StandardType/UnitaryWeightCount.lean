module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.NormNum

public section

namespace CFSG.StandardType

namespace UnitaryWeight

open Matrix Finset

section Support

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]

lemma sum_extendByZero_mul {I : Finset ι} (z : I → K) (g : ι → K) :
    (∑ α : ι, (if h : α ∈ I then z ⟨α, h⟩ else 0) * g α) = ∑ α : I, z α * g α := by
  rw [← Finset.sum_subset (Finset.subset_univ I) (fun α _ hα => by simp [dif_neg hα])]
  rw [Finset.sum_subtype I (fun x => Iff.rfl)
    (fun α => (if h : α ∈ I then z ⟨α, h⟩ else 0) * g α)]
  apply Finset.sum_congr rfl
  intro α _
  simp

theorem card_le_card_of_isUnit_support {H : Matrix ι ι K} (hH : IsUnit H) {I I' : Finset ι}
    (hsupp : ∀ α ∈ I, ∀ β, β ∉ I' → H α β = 0) : I.card ≤ I'.card := by
  let M : Matrix I I' K := H.submatrix (↑) (↑)
  let φ : (I → K) →ₗ[K] (I' → K) := M.vecMulLinear
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hsub : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hz' : (x - y) ᵥ* M = 0 := hsub
    let zhat : ι → K := fun α => if h : α ∈ I then (x - y) ⟨α, h⟩ else 0
    have hzh : zhat ᵥ* H = 0 := by
      funext β
      rw [Matrix.vecMul_apply_eq_sum]
      by_cases hβ : β ∈ I'
      · have hthis : (∑ α : I, (x - y) α * H (α : ι) β) = 0 := by
          have hcf := congrFun hz' ⟨β, hβ⟩
          rw [Matrix.vecMul_apply_eq_sum] at hcf
          simpa [M] using hcf
        rw [show (∑ α : ι, zhat α * H α β)
            = ∑ α : I, (x - y) α * H (α : ι) β from by
          rw [sum_extendByZero_mul]]
        simpa using hthis
      · apply Finset.sum_eq_zero
        intro α _
        by_cases hα : α ∈ I
        · have hH0 : H α β = 0 := hsupp α hα β hβ
          simp [zhat, dif_pos hα, hH0]
        · simp [zhat, dif_neg hα]
    have hzero : zhat = 0 := (Matrix.vecMul_injective_of_isUnit hH) (by simpa using hzh)
    have hz : x - y = 0 := by
      funext α
      have hcf := congrFun hzero (α : ι)
      simpa [zhat, dif_pos α.2] using hcf
    exact sub_eq_zero.mp hz
  have hle := LinearMap.finrank_le_finrank_of_injective hφinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hle
  simpa using hle

end Support

section Combinatorics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma zmod_three_cases (z : ZMod 3) : z = 0 ∨ z = 1 ∨ z = 2 := by
  revert z; decide

lemma sum_univ_zmod_three (f : ZMod 3 → ℕ) : (∑ a : ZMod 3, f a) = f 0 + f 1 + f 2 := by
  have h : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [h]
  rw [Finset.sum_insert (by decide : (0 : ZMod 3) ∉ ({1, 2} : Finset (ZMod 3)))]
  rw [Finset.sum_insert (by decide : (1 : ZMod 3) ∉ ({2} : Finset (ZMod 3)))]
  rw [Finset.sum_singleton]
  ring

theorem card_fiber_bounds_zmod3 (x y : ι → ZMod 3)
    (hspan : ∀ i j : ZMod 3, (i ≠ 0 ∨ j ≠ 0) → ∃ α β, i * x α + j * y α ≠ i * x β + j * y β)
    (hsym : ∀ u v : ZMod 3,
      (univ.filter fun α => x α = u ∧ y α = v).card =
        (univ.filter fun α => x α = -u ∧ y α = -v).card) :
    (univ.filter fun α => x α = 0 ∧ y α = 0).card + 4 ≤ Fintype.card ι ∧
      ∀ u v : ZMod 3, (u ≠ 0 ∨ v ≠ 0) →
        2 * (univ.filter fun α => x α = u ∧ y α = v).card + 2 ≤ Fintype.card ι := by
  let d : ZMod 3 × ZMod 3 → ℕ := fun t => (univ.filter fun α => x α = t.1 ∧ y α = t.2).card
  have hsum : (∑ t : ZMod 3 × ZMod 3, d t) = Fintype.card ι := by
    rw [← Finset.card_univ (α := ι)]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun α => (x α, y α))
      (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro t _
    simp [d, Prod.ext_iff]
  have hneg : ∀ t, d (-t) = d t := by
    rintro ⟨u, v⟩
    exact (hsym u v).symm
  have hd20 : d (2,0) = d (1,0) := by
    have h : d ((-(1 : ZMod 3), -(0 : ZMod 3)) : ZMod 3 × ZMod 3) = d (1,0) := hneg (1,0)
    have e : ((-(1 : ZMod 3), -(0 : ZMod 3)) : ZMod 3 × ZMod 3) = (2,0) := by decide
    rw [e] at h; exact h
  have hd21 : d (2,1) = d (1,2) := by
    have h : d ((-(1 : ZMod 3), -(2 : ZMod 3)) : ZMod 3 × ZMod 3) = d (1,2) := hneg (1,2)
    have e : ((-(1 : ZMod 3), -(2 : ZMod 3)) : ZMod 3 × ZMod 3) = (2,1) := by decide
    rw [e] at h; exact h
  have hd22 : d (2,2) = d (1,1) := by
    have h : d ((-(1 : ZMod 3), -(1 : ZMod 3)) : ZMod 3 × ZMod 3) = d (1,1) := hneg (1,1)
    have e : ((-(1 : ZMod 3), -(1 : ZMod 3)) : ZMod 3 × ZMod 3) = (2,2) := by decide
    rw [e] at h; exact h
  have hd02 : d (0,2) = d (0,1) := by
    have h : d ((-(0 : ZMod 3), -(1 : ZMod 3)) : ZMod 3 × ZMod 3) = d (0,1) := hneg (0,1)
    have e : ((-(0 : ZMod 3), -(1 : ZMod 3)) : ZMod 3 × ZMod 3) = (0,2) := by decide
    rw [e] at h; exact h
  have hsum9 : (∑ t : ZMod 3 × ZMod 3, d t) =
      d (0,0) + d (0,1) + d (0,2) + d (1,0) + d (1,1) + d (1,2)
        + d (2,0) + d (2,1) + d (2,2) := by
    rw [Fintype.sum_prod_type]
    rw [sum_univ_zmod_three (f := fun a => ∑ b : ZMod 3, d (a, b))]
    rw [sum_univ_zmod_three (f := fun b => d (0, b))]
    rw [sum_univ_zmod_three (f := fun b => d (1, b))]
    rw [sum_univ_zmod_three (f := fun b => d (2, b))]
    ring
  have hx_ne : ∃ α, x α ≠ 0 := by
    obtain ⟨α, β, hαβ⟩ := hspan 1 0 (Or.inl (by decide : (1 : ZMod 3) ≠ 0))
    simp only [one_mul, zero_mul, add_zero] at hαβ
    rcases eq_or_ne (x α) 0 with h | h
    · exact ⟨β, fun hb => hαβ (by rw [h, hb])⟩
    · exact ⟨α, h⟩
  have hy_ne : ∃ α, y α ≠ 0 := by
    obtain ⟨α, β, hαβ⟩ := hspan 0 1 (Or.inr (by decide : (1 : ZMod 3) ≠ 0))
    simp only [zero_mul, one_mul, zero_add] at hαβ
    rcases eq_or_ne (y α) 0 with h | h
    · exact ⟨β, fun hb => hαβ (by rw [h, hb])⟩
    · exact ⟨α, h⟩
  have hxy_ne : ∃ α, x α + y α ≠ 0 := by
    obtain ⟨α, β, hαβ⟩ := hspan 1 1 (Or.inl (by decide : (1 : ZMod 3) ≠ 0))
    simp only [one_mul] at hαβ
    rcases eq_or_ne (x α + y α) 0 with h | h
    · exact ⟨β, fun hb => hαβ (by rw [h, hb])⟩
    · exact ⟨α, h⟩
  have hxy2_ne : ∃ α, x α + 2 * y α ≠ 0 := by
    obtain ⟨α, β, hαβ⟩ := hspan 1 2 (Or.inl (by decide : (1 : ZMod 3) ≠ 0))
    simp only [one_mul] at hαβ
    rcases eq_or_ne (x α + 2 * y α) 0 with h | h
    · exact ⟨β, fun hb => hαβ (by rw [h, hb])⟩
    · exact ⟨α, h⟩
  have pos_of : ∀ (α : ι), 0 < d (x α, y α) := by
    intro α
    show 0 < (univ.filter fun γ => x γ = x α ∧ y γ = y α).card
    exact Finset.card_pos.mpr ⟨α, by simp⟩
  have hP1 : 0 < d (1,0) ∨ 0 < d (1,1) ∨ 0 < d (1,2) := by
    obtain ⟨α, hα⟩ := hx_ne
    have ht := pos_of α
    rcases zmod_three_cases (x α) with hx | hx | hx
    · exact absurd hx hα
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · left; rw [hy] at ht; exact ht
      · right; left; rw [hy] at ht; exact ht
      · right; right; rw [hy] at ht; exact ht
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · left; rw [hy, hd20] at ht; exact ht
      · right; right; rw [hy, hd21] at ht; exact ht
      · right; left; rw [hy, hd22] at ht; exact ht
  have hP2 : 0 < d (0,1) ∨ 0 < d (1,1) ∨ 0 < d (1,2) := by
    obtain ⟨α, hα⟩ := hy_ne
    have ht := pos_of α
    rcases zmod_three_cases (y α) with hy | hy | hy
    · exact absurd hy hα
    · rw [hy] at ht
      rcases zmod_three_cases (x α) with hx | hx | hx
      · left; rw [hx] at ht; exact ht
      · right; left; rw [hx] at ht; exact ht
      · right; right; rw [hx, hd21] at ht; exact ht
    · rw [hy] at ht
      rcases zmod_three_cases (x α) with hx | hx | hx
      · left; rw [hx, hd02] at ht; exact ht
      · right; right; rw [hx] at ht; exact ht
      · right; left; rw [hx, hd22] at ht; exact ht
  have hP3 : 0 < d (1,0) ∨ 0 < d (0,1) ∨ 0 < d (1,1) := by
    obtain ⟨α, hα⟩ := hxy_ne
    have ht := pos_of α
    rcases zmod_three_cases (x α) with hx | hx | hx
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · exact absurd (by rw [hx, hy]; decide) hα
      · right; left; rw [hy] at ht; exact ht
      · right; left; rw [hy, hd02] at ht; exact ht
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · left; rw [hy] at ht; exact ht
      · right; right; rw [hy] at ht; exact ht
      · exact absurd (by rw [hx, hy]; decide) hα
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · left; rw [hy, hd20] at ht; exact ht
      · exact absurd (by rw [hx, hy]; decide) hα
      · right; right; rw [hy, hd22] at ht; exact ht
  have hP4 : 0 < d (1,0) ∨ 0 < d (0,1) ∨ 0 < d (1,2) := by
    obtain ⟨α, hα⟩ := hxy2_ne
    have ht := pos_of α
    rcases zmod_three_cases (x α) with hx | hx | hx
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · exact absurd (by rw [hx, hy]; decide) hα
      · right; left; rw [hy] at ht; exact ht
      · right; left; rw [hy, hd02] at ht; exact ht
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · left; rw [hy] at ht; exact ht
      · exact absurd (by rw [hx, hy]; decide) hα
      · right; right; rw [hy] at ht; exact ht
    · rw [hx] at ht
      rcases zmod_three_cases (y α) with hy | hy | hy
      · left; rw [hy, hd20] at ht; exact ht
      · right; right; rw [hy, hd21] at ht; exact ht
      · exact absurd (by rw [hx, hy]; decide) hα
  have hAB : 2 ≤ d (1,0) + d (0,1) + d (1,1) + d (1,2) := by
    rcases hP1 with h | h | h <;> rcases hP2 with h' | h' | h' <;> omega
  have hP1s : 1 ≤ d (1,0) + d (1,1) + d (1,2) := by
    rcases hP1 with h | h | h <;> omega
  have hP2s : 1 ≤ d (0,1) + d (1,1) + d (1,2) := by
    rcases hP2 with h | h | h <;> omega
  have hP3s : 1 ≤ d (1,0) + d (0,1) + d (1,1) := by
    rcases hP3 with h | h | h <;> omega
  have hP4s : 1 ≤ d (1,0) + d (0,1) + d (1,2) := by
    rcases hP4 with h | h | h <;> omega
  have hn : Fintype.card ι = d (0,0) + 2 * (d (1,0) + d (0,1) + d (1,1) + d (1,2)) := by
    rw [← hsum, hsum9, hd20, hd21, hd22, hd02]
    ring
  constructor
  · show d (0,0) + 4 ≤ Fintype.card ι
    omega
  · intro u v huv
    change 2 * d (u, v) + 2 ≤ Fintype.card ι
    rcases zmod_three_cases u with hu | hu | hu <;> rcases zmod_three_cases v with hv | hv | hv
    · rw [hu, hv] at huv; simp at huv
    · rw [hu, hv]; omega
    · rw [hu, hv]; omega
    · rw [hu, hv]; omega
    · rw [hu, hv]; omega
    · rw [hu, hv]; omega
    · rw [hu, hv]; omega
    · rw [hu, hv]; omega
    · rw [hu, hv]; omega

lemma zeta_pow_val_add {Ω : Type*} [Field Ω] {ζ : Ω} (hζ3 : ζ ^ 3 = 1) (i j : ZMod 3) :
    ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod (i.val + j.val) hζ3, pow_add]

lemma zeta_pow_val_pow {Ω : Type*} [Field Ω] {ζ : Ω} (hζ3 : ζ ^ 3 = 1) (m : ℕ) (k : ZMod 3) :
    (ζ ^ k.val) ^ m = ζ ^ ((m : ZMod 3) * k).val := by
  rw [← pow_mul, ZMod.val_mul, ZMod.val_natCast, pow_eq_pow_mod (k.val * m) hζ3]
  congr 1
  rw [Nat.mul_comm k.val m, Nat.mul_mod, Nat.mod_eq_of_lt (ZMod.val_lt k)]

lemma zeta_pow_val_inv {Ω : Type*} [Field Ω] {ζ : Ω} (hζ3 : ζ ^ 3 = 1) (k : ZMod 3) :
    (ζ ^ k.val)⁻¹ = ζ ^ (-k).val := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add, pow_eq_pow_mod (k.val + (-k).val) hζ3, ← ZMod.val_add]
  simp

lemma cube_root_trichotomy {Ω : Type*} [Field Ω] {ζ : Ω} (hζ2 : ζ ^ 2 + ζ + 1 = 0)
    (hζ3 : ζ ^ 3 = 1) {η : Ω} (hη : η ^ 3 = 1) : η = 1 ∨ η = ζ ∨ η = ζ ^ 2 := by
  have h : (η - 1) * (η - ζ) * (η - ζ^2) = 0 := by
    have hh : (η - 1) * (η - ζ) * (η - ζ^2) = η^3 - 1 := by
      linear_combination (η - η^2) * hζ2 + (η - 1) * hζ3
    rw [hh, hη]; ring
  rcases mul_eq_zero.mp h with h' | h'
  · rcases mul_eq_zero.mp h' with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
  · exact Or.inr (Or.inr (sub_eq_zero.mp h'))

lemma zeta_pow_val_injective {Ω : Type*} [Field Ω] {ζ : Ω} (hζ1 : ζ ≠ 1)
    (hζ2 : ζ ^ 2 + ζ + 1 = 0) (hζ3 : ζ ^ 3 = 1) :
    Function.Injective (fun k : ZMod 3 => ζ ^ k.val) := by
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ3; norm_num at hζ3
  have h1ζ : (1 : Ω) ≠ ζ := fun h => hζ1 h.symm
  have hζζ2 : ζ ≠ ζ ^ 2 := by
    intro h
    have h0 : ζ * (1 - ζ) = 0 := by
      rw [show ζ * (1 - ζ) = ζ - ζ^2 by ring, sub_eq_zero]; exact h
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact hζ0 h'
    · exact hζ1 (sub_eq_zero.mp h').symm
  have h1ζ2 : (1 : Ω) ≠ ζ ^ 2 := by
    intro h
    have h' : ζ = 1 := by
      calc ζ = ζ * 1 := by ring
        _ = ζ * ζ^2 := by rw [h]
        _ = ζ^3 := by ring
        _ = 1 := hζ3
    exact hζ1 h'
  have e0 : ζ ^ (0 : ZMod 3).val = 1 := by rw [show (0 : ZMod 3).val = 0 by decide, pow_zero]
  have e1 : ζ ^ (1 : ZMod 3).val = ζ := by rw [show (1 : ZMod 3).val = 1 by decide, pow_one]
  have e2 : ζ ^ (2 : ZMod 3).val = ζ^2 := by rw [show (2 : ZMod 3).val = 2 by decide]
  intro i j hij
  rcases zmod_three_cases i with hi | hi | hi <;> rcases zmod_three_cases j with hj | hj | hj <;>
    rw [hi, hj] at hij ⊢ <;> simp only [e0, e1, e2] at hij
  all_goals (first
    | rfl
    | exact absurd hij h1ζ
    | exact absurd hij h1ζ.symm
    | exact absurd hij h1ζ2
    | exact absurd hij h1ζ2.symm
    | exact absurd hij hζζ2
    | exact absurd hij hζζ2.symm
    | exact absurd hij hζ1
    | exact absurd hij hζ1.symm)

variable {Ω : Type*} [Field Ω] [DecidableEq Ω]

theorem card_fiber_bounds (a b : ι → Ω) (ha : ∀ α, a α ^ 3 = 1) (hb : ∀ α, b α ^ 3 = 1)
    (hspan : ∀ i j : ℕ, ¬ (3 ∣ i ∧ 3 ∣ j) → ∃ α β, a α ^ i * b α ^ j ≠ a β ^ i * b β ^ j)
    (hsym : ∀ u v : Ω,
      (univ.filter fun α => a α = u ∧ b α = v).card =
        (univ.filter fun α => a α = u⁻¹ ∧ b α = v⁻¹).card) :
    (univ.filter fun α => a α = 1 ∧ b α = 1).card + 4 ≤ Fintype.card ι ∧
      ∀ u v : Ω, (u ≠ 1 ∨ v ≠ 1) →
        2 * (univ.filter fun α => a α = u ∧ b α = v).card + 2 ≤ Fintype.card ι := by
  have h_exists : ∃ α, a α ≠ 1 := by
    by_contra h
    push Not at h
    obtain ⟨α, β, hαβ⟩ := hspan 1 0 (by decide : ¬ (3 ∣ 1 ∧ 3 ∣ 0))
    simp only [pow_one, pow_zero, mul_one] at hαβ
    exact hαβ (by rw [h α, h β])
  obtain ⟨α₀, hα₀⟩ := h_exists
  set ζ : Ω := a α₀ with hζdef
  have hζ1 : ζ ≠ 1 := hα₀
  have hζ3 : ζ ^ 3 = 1 := ha α₀
  have hζ0 : ζ ≠ 0 := by intro h; rw [h] at hζ3; norm_num at hζ3
  have hζ2 : ζ ^ 2 + ζ + 1 = 0 := by
    have h : (ζ - 1) * (ζ^2 + ζ + 1) = 0 := by
      have hh : (ζ - 1) * (ζ^2 + ζ + 1) = ζ^3 - 1 := by ring
      rw [hh, hζ3]; ring
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (sub_eq_zero.mp h') hζ1
    · exact h'
  let e : ZMod 3 → Ω := fun k => ζ ^ k.val
  have he0 : e 0 = 1 := by
    show ζ ^ (0 : ZMod 3).val = 1
    rw [show (0 : ZMod 3).val = 0 by decide, pow_zero]
  have he1 : e 1 = ζ := by
    show ζ ^ (1 : ZMod 3).val = ζ
    rw [show (1 : ZMod 3).val = 1 by decide, pow_one]
  have he2 : e 2 = ζ^2 := by
    show ζ ^ (2 : ZMod 3).val = ζ^2
    rw [show (2 : ZMod 3).val = 2 by decide]
  have heinj : Function.Injective e := zeta_pow_val_injective hζ1 hζ2 hζ3
  have headd : ∀ i j : ZMod 3, e (i + j) = e i * e j := fun i j => zeta_pow_val_add hζ3 i j
  have hepow : ∀ (m : ℕ) (k : ZMod 3), (e k) ^ m = e ((m : ZMod 3) * k) :=
    fun m k => zeta_pow_val_pow hζ3 m k
  have heinv : ∀ k : ZMod 3, (e k)⁻¹ = e (-k) := fun k => zeta_pow_val_inv hζ3 k
  have ha_cube : ∀ α, ∃ k : ZMod 3, e k = a α := by
    intro α
    rcases cube_root_trichotomy hζ2 hζ3 (ha α) with h | h | h
    · exact ⟨0, by rw [he0, h]⟩
    · exact ⟨1, by rw [he1, h]⟩
    · exact ⟨2, by rw [he2, h]⟩
  have hb_cube : ∀ α, ∃ k : ZMod 3, e k = b α := by
    intro α
    rcases cube_root_trichotomy hζ2 hζ3 (hb α) with h | h | h
    · exact ⟨0, by rw [he0, h]⟩
    · exact ⟨1, by rw [he1, h]⟩
    · exact ⟨2, by rw [he2, h]⟩
  let x : ι → ZMod 3 := fun α => Classical.choose (ha_cube α)
  have hx : ∀ α, e (x α) = a α := fun α => Classical.choose_spec (ha_cube α)
  let y : ι → ZMod 3 := fun α => Classical.choose (hb_cube α)
  have hy : ∀ α, e (y α) = b α := fun α => Classical.choose_spec (hb_cube α)
  have ha_pow : ∀ (α : ι) (m : ℕ), a α ^ m = e ((m : ZMod 3) * x α) := by
    intro α m
    rw [← hx α]
    exact hepow m (x α)
  have hb_pow : ∀ (α : ι) (m : ℕ), b α ^ m = e ((m : ZMod 3) * y α) := by
    intro α m
    rw [← hy α]
    exact hepow m (y α)
  have hspan' : ∀ i j : ZMod 3, (i ≠ 0 ∨ j ≠ 0) →
      ∃ α β, i * x α + j * y α ≠ i * x β + j * y β := by
    intro i j hij
    have hdiv : ¬ (3 ∣ i.val ∧ 3 ∣ j.val) := by
      rintro ⟨hi, hj⟩
      have hi0 : i.val = 0 := Nat.eq_zero_of_dvd_of_lt hi (ZMod.val_lt i)
      have hj0 : j.val = 0 := Nat.eq_zero_of_dvd_of_lt hj (ZMod.val_lt j)
      rw [ZMod.val_eq_zero] at hi0 hj0
      rcases hij with h | h
      · exact h hi0
      · exact h hj0
    obtain ⟨α, β, hαβ⟩ := hspan i.val j.val hdiv
    refine ⟨α, β, ?_⟩
    intro heq
    have hEq : a α ^ i.val * b α ^ j.val = a β ^ i.val * b β ^ j.val := by
      rw [ha_pow α i.val, hb_pow α j.val, ha_pow β i.val, hb_pow β j.val]
      rw [← headd ((i.val : ZMod 3) * x α) ((j.val : ZMod 3) * y α),
          ← headd ((i.val : ZMod 3) * x β) ((j.val : ZMod 3) * y β)]
      rw [ZMod.natCast_zmod_val i, ZMod.natCast_zmod_val j, heq]
    exact hαβ hEq
  have hsym' : ∀ u v : ZMod 3,
      (univ.filter fun α => x α = u ∧ y α = v).card =
        (univ.filter fun α => x α = -u ∧ y α = -v).card := by
    intro u v
    have h := hsym (e u) (e v)
    have hfil1 : (univ.filter fun α => a α = e u ∧ b α = e v) =
        (univ.filter fun α => x α = u ∧ y α = v) := by
      apply Finset.filter_congr
      intro α _
      simp only [← hx α, ← hy α, heinj.eq_iff]
    have hfil2 : (univ.filter fun α => a α = (e u)⁻¹ ∧ b α = (e v)⁻¹) =
        (univ.filter fun α => x α = -u ∧ y α = -v) := by
      apply Finset.filter_congr
      intro α _
      rw [heinv u, heinv v]
      simp only [← hx α, ← hy α, heinj.eq_iff]
    rw [hfil1, hfil2] at h
    exact h
  have hz := card_fiber_bounds_zmod3 x y hspan' hsym'
  have hn2 : 2 ≤ Fintype.card ι := by have := hz.1; omega
  refine ⟨?_, ?_⟩
  · have hfil : (univ.filter fun α => a α = 1 ∧ b α = 1) =
        (univ.filter fun α => x α = 0 ∧ y α = 0) := by
      apply Finset.filter_congr
      intro α _
      simp only [← he0, ← hx α, ← hy α, heinj.eq_iff]
    rw [hfil]; exact hz.1
  · intro u v huv
    by_cases hu : ∃ u' : ZMod 3, e u' = u
    · by_cases hv : ∃ v' : ZMod 3, e v' = v
      · obtain ⟨u', hu'⟩ := hu
        obtain ⟨v', hv'⟩ := hv
        have hfil : (univ.filter fun α => a α = u ∧ b α = v) =
            (univ.filter fun α => x α = u' ∧ y α = v') := by
          apply Finset.filter_congr
          intro α _
          simp only [← hu', ← hv', ← hx α, ← hy α, heinj.eq_iff]
        have huv' : u' ≠ 0 ∨ v' ≠ 0 := by
          rcases huv with h | h
          · left; intro h0; exact h (by rw [← hu', h0, he0])
          · right; intro h0; exact h (by rw [← hv', h0, he0])
        rw [hfil]; exact hz.2 u' v' huv'
      · have hempty : (univ.filter fun α => a α = u ∧ b α = v) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro α _
          rintro ⟨_, h2⟩
          exact hv ⟨y α, by rw [hy α, h2]⟩
        rw [hempty]; simp only [Finset.card_empty, mul_zero, zero_add]; omega
    · have hempty : (univ.filter fun α => a α = u ∧ b α = v) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro α _
        rintro ⟨h1, _⟩
        exact hu ⟨x α, by rw [hx α, h1]⟩
      rw [hempty]; simp only [Finset.card_empty, mul_zero, zero_add]; omega

end Combinatorics

end UnitaryWeight

end CFSG.StandardType

end

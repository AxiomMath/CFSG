module

import Mathlib.Tactic.LinearCombination
public import CFSG.RankThree.PartOne.N1322.CoreData
public import CFSG.RankThree.PartOne.N1322.MonoRefl

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open Equiv

variable {K : Type*} [Field K]

theorem perm_fix2 : ∀ σ : Perm (Fin 3), σ 2 = 2 → σ = 1 ∨ σ = swap 0 1 := by decide

theorem perm_zero_two : ∀ σ : Perm (Fin 3), σ 0 = 2 →
    (σ⁻¹ 0 = 2 ∧ σ⁻¹ 1 = 1) ∨ (σ⁻¹ 0 = 1 ∧ σ⁻¹ 1 = 2) := by decide

theorem swap01_zpow_even (m : ℤ) : (swap (0 : Fin 3) 1) ^ (2 * m) = 1 := by
  rw [zpow_mul, zpow_two, swap_mul_self, one_zpow]

theorem swap01_zpow_odd (m : ℤ) : (swap (0 : Fin 3) 1) ^ (2 * m + 1) = swap 0 1 := by
  rw [zpow_add_one, swap01_zpow_even, one_mul]

theorem mono_one_comm (a b : Fin 3 → Kˣ) :
    (mono 1 a : GL (Fin 3) K) * mono 1 b = mono 1 b * mono 1 a := by
  rw [mono_mul, mono_mul]
  exact congrArg (mono 1) (funext fun j => by simp only [Perm.one_apply]; exact mul_comm _ _)

theorem HasPerm.comm_of_one {g g' : GL (Fin 3) K} (h : HasPerm g 1) (h' : HasPerm g' 1) :
    g * g' = g' * g := by
  obtain ⟨a, rfl⟩ := h
  obtain ⟨b, rfl⟩ := h'
  exact mono_one_comm a b

theorem aU_eq_of_swap01 {b : Fin 3 → Kˣ} (hb2 : b 2 = 1) (hb : b 1 * b 0 = 1) :
    b = aU 0 1 (b 0) := by
  funext m
  fin_cases m
  · simp [aU]
  · simp [aU]
    exact eq_inv_of_mul_eq_one_left hb
  · simp [aU]
    exact hb2

theorem aU_left {i j : Fin 3} (r : Kˣ) : aU i j r i = r := by simp [aU]

theorem aU_right {i j : Fin 3} (hij : i ≠ j) (r : Kˣ) : aU i j r j = r⁻¹ := by
  simp [aU, hij.symm]

theorem aU_other {i j m : Fin 3} (hmi : m ≠ i) (hmj : m ≠ j) (r : Kˣ) : aU i j r m = 1 := by
  simp [aU, hmi, hmj]

theorem aref_mul_aref {i j : Fin 3} (hij : i ≠ j) (r s : Kˣ) :
    (aref i j r : GL (Fin 3) K) * aref i j s = mono 1 (aU i j (r⁻¹ * s)) := by
  unfold aref
  rw [mono_mul, swap_mul_self]
  refine congrArg (mono 1) (funext fun m => ?_)
  by_cases hmi : m = i
  · subst hmi
    rw [swap_apply_left, aU_right hij, aU_left, aU_left]
  · by_cases hmj : m = j
    · subst hmj
      rw [swap_apply_right, aU_left, aU_right hij, aU_right hij, mul_inv_rev, inv_inv, mul_comm]
    · rw [swap_apply_of_ne_of_ne hmi hmj, aU_other hmi hmj, aU_other hmi hmj,
        aU_other hmi hmj, mul_one]

theorem diag_conj_aref {i j : Fin 3} (hij : i ≠ j) (d : Fin 3 → Kˣ) (r : Kˣ) :
    (mono 1 d : GL (Fin 3) K) * aref i j r * (mono 1 d)⁻¹ = aref i j (d j * r * (d i)⁻¹) := by
  rw [aref, mono_conj_diag, aref]
  refine congrArg (mono (swap i j)) (funext fun m => ?_)
  by_cases hmi : m = i
  · subst hmi
    rw [swap_apply_left, aU_left, aU_left]
  · by_cases hmj : m = j
    · subst hmj
      rw [swap_apply_right, aU_right hij, aU_right hij]
      group
    · rw [swap_apply_of_ne_of_ne hmi hmj, aU_other hmi hmj, aU_other hmi hmj, mul_one,
        mul_inv_cancel]

theorem closure_top_of_closure_eq {G : Type*} [Group G] (H : Subgroup G) (D : Set G)
    (h : Subgroup.closure (D ∩ (H : Set G)) = H) :
    Subgroup.closure {x : H | (x : G) ∈ D} = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : H.subtype '' {x : H | (x : G) ∈ D} = D ∩ (H : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨hy, hyH⟩
      exact ⟨⟨y, hyH⟩, hy, rfl⟩
  rw [this, h]

theorem IsRefl.eigen_minus (h2 : (2 : K) ≠ 0) {g : GL (Fin 3) K} {r φ : Fin 3 → K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = 1 - Matrix.vecMulVec r φ) {v : Fin 3 → K}
    (hv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = -v) : ∃ μ : K, v = μ • r := by
  rw [IsRefl.mulVec_apply hg] at hv
  refine ⟨(φ ⬝ᵥ v) / 2, ?_⟩
  have h3 : (2 : K) • v = (φ ⬝ᵥ v) • r := by
    rw [two_smul]
    exact (eq_neg_add_iff_add_eq).mp (sub_eq_iff_eq_add.mp hv)
  calc v = (2 : K)⁻¹ • ((2 : K) • v) := by rw [smul_smul, inv_mul_cancel₀ h2, one_smul]
    _ = (2 : K)⁻¹ • ((φ ⬝ᵥ v) • r) := by rw [h3]
    _ = ((φ ⬝ᵥ v) / 2) • r := by rw [smul_smul, div_eq_inv_mul]

theorem neg_one_ne_one (h2 : (2 : K) ≠ 0) : (-1 : Kˣ) ≠ 1 := by
  intro h
  apply h2
  have := congrArg Units.val h
  simp only [Units.val_neg, Units.val_one] at this
  linear_combination -this

theorem aU_inv (i j : Fin 3) (r : Kˣ) : (fun m => (aU i j r m)⁻¹) = aU i j r⁻¹ := by
  funext m
  unfold aU
  split_ifs <;> simp

theorem hcover_of_hyp (h2 : (2 : K) ≠ 0) {d : CoreData K} (h : MonoHyp d) :
    ∀ x : d.Lm, IsNCInv x → (x : GL (Fin 3) K) ∈ d.D := by
  obtain ⟨e⟩ := h.Ldih
  have hS : ∀ x ∈ {x : d.Lm | (x : GL (Fin 3) K) ∈ d.D}, IsNCInv x := by
    intro x hx
    have hxD : (x : GL (Fin 3) K) ∈ d.D := hx
    have hrefl := h.refl _ hxD
    refine ⟨?_, ?_, ?_⟩
    · apply Subtype.ext
      simpa using hrefl.sq
    · intro h1
      have h3 := hrefl.trace_eq
      rw [h1] at h3
      simp at h3
      apply h2
      linear_combination h3
    · by_contra hcen
      push Not at hcen
      obtain ⟨r, φ, hr, hφ, hg⟩ := hrefl
      have hxr : (x : GL (Fin 3) K).val *ᵥ r = -r := IsRefl.mulVec_root hφ hg
      have hline : ∀ l ∈ d.Lm, ∃ μ : K, (l : Matrix (Fin 3) (Fin 3) K) *ᵥ r = μ • r := by
        intro l hl
        have hcomm : (x : GL (Fin 3) K) * l = l * x := congrArg Subtype.val (hcen ⟨l, hl⟩)
        refine IsRefl.eigen_minus h2 hg ?_
        have h4 : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
            ((l : Matrix (Fin 3) (Fin 3) K) *ᵥ r) =
            (l : Matrix (Fin 3) (Fin 3) K) *ᵥ (((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ r) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hcomm]
        rw [h4, hxr, Matrix.mulVec_neg]
      obtain ⟨ν, hν⟩ := h.lines r hr hline
      have hxc := h.c_fix x x.2
      have hν0 : ν ≠ 0 := by
        rintro rfl
        apply hr
        rw [hν, zero_smul]
      obtain ⟨j, hj⟩ : ∃ j, d.c j ≠ 0 := by
        by_contra hno
        push Not at hno
        exact h.c_ne (funext hno)
      rw [hν, Matrix.mulVec_smul, hxc] at hxr
      have h5 := congrFun hxr j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h5
      have h6 : (2 : K) * (ν * d.c j) = 0 := by linear_combination h5
      exact absurd h6 (mul_ne_zero h2 (mul_ne_zero hν0 hj))
  have hcov := refl_cover h.n_mem e {x : d.Lm | (x : GL (Fin 3) K) ∈ d.D} hS
    (by
      intro x hx g
      have hxD : (x : GL (Fin 3) K) ∈ d.D := hx
      show ((g * x * g⁻¹ : d.Lm) : GL (Fin 3) K) ∈ d.D
      have := h.Dconj (g : GL (Fin 3) K) (h.Lle g.2) _ hxD
      simpa using this)
    (closure_top_of_closure_eq d.Lm d.D h.Lgen)
  intro x hx
  exact hcov x hx

end CFSG.RankThree.PartOne.N1322

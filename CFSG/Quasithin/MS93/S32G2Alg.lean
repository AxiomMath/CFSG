module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.Quasithin.MS93.S32

open scoped Matrix

variable {F : Type} [Field F]

@[expose] def a1Pair (x y : Fin 3 → F) : Fin 3 → F :=
  ![y 1 * x 1 + y 2 * x 2 + y 0 * y 0 * x 0, y 1 * x 0 + y 0 * x 2, y 2 * x 0 + y 0 * x 1]

@[expose] def a1Mat (y : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  !![y 0 * y 0, y 1, y 2; y 1, 0, y 0; y 2, y 0, 0]

theorem a1Pair_eq_mulVec (x y : Fin 3 → F) : a1Pair x y = a1Mat y *ᵥ x := by
  ext i
  fin_cases i
  · simp [a1Pair, a1Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · simp [a1Pair, a1Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · simp [a1Pair, a1Mat, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem a1Pair_smul_left (c : F) (x y : Fin 3 → F) : a1Pair (c • x) y = c • a1Pair x y := by
  rw [a1Pair_eq_mulVec, a1Pair_eq_mulVec, Matrix.mulVec_smul]

theorem a1Pair_e0 (y : Fin 3 → F) : a1Pair ![1, 0, 0] y = ![y 0 * y 0, y 1, y 2] := by
  ext i
  fin_cases i <;> simp [a1Pair]

theorem a1Pair_e1 (y : Fin 3 → F) : a1Pair ![0, 1, 0] y = ![y 1, 0, y 0] := by
  ext i
  fin_cases i <;> simp [a1Pair]

theorem a1Pair_e2 (y : Fin 3 → F) : a1Pair ![0, 0, 1] y = ![y 2, y 0, 0] := by
  ext i
  fin_cases i <;> simp [a1Pair]

theorem a1Pair_one (x : Fin 3 → F) : a1Pair x ![1, 0, 0] = ![x 0, x 2, x 1] := by
  ext i
  fin_cases i <;> simp [a1Pair]

variable [CharP F 2]

theorem frob3_injective :
    Function.Injective (fun y : Fin 3 → F => ![y 0 * y 0, y 1, y 2]) := by
  intro y y' h
  have h0 : y 0 * y 0 = y' 0 * y' 0 := congrFun h 0
  have h1 : y 1 = y' 1 := congrFun h 1
  have h2 : y 2 = y' 2 := congrFun h 2
  have h0' : y 0 = y' 0 := by
    have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
    have hs : (y 0 + y' 0) * (y 0 + y' 0) = 0 := by
      linear_combination h0 + (y 0 * y' 0 + y' 0 * y' 0) * h2F
    have := mul_self_eq_zero.mp hs
    exact (CharTwo.add_eq_zero.mp this)
  ext i
  fin_cases i
  · exact h0'
  · exact h1
  · exact h2

theorem eq_zero_or_eq_one_of_a1Pair [Finite F] (Φ : (Fin 3 → F) →+ (Fin 3 → F))
    (hΦ : Function.Injective Φ) (g h : (Fin 3 → F) → (Fin 3 → F))
    (hgh : ∀ x y, Φ (a1Pair x y) = a1Pair (g y) (h x)) (c : F) : c = 0 ∨ c = 1 := by
  classical
  set fr : (Fin 3 → F) → (Fin 3 → F) := fun y => ![y 0 * y 0, y 1, y 2] with hfr
  have hfr_inj : Function.Injective fr := frob3_injective
  have hfr_surj : Function.Surjective fr := Finite.injective_iff_surjective.mp hfr_inj
  have hh : Function.Injective h := by
    intro x x' hxx
    have e := hgh x ![1, 0, 0]
    have e' := hgh x' ![1, 0, 0]
    rw [hxx, ← e'] at e
    have := hΦ e
    rw [a1Pair_one, a1Pair_one] at this
    ext i
    fin_cases i
    · exact congrFun this 0
    · exact congrFun this 2
    · exact congrFun this 1
  have hh_surj : Function.Surjective h := Finite.injective_iff_surjective.mp hh
  have hg : Function.Injective g := by
    intro y y' hyy
    have e := hgh ![1, 0, 0] y
    have e' := hgh ![1, 0, 0] y'
    rw [hyy, ← e', a1Pair_e0, a1Pair_e0] at e
    exact hfr_inj (hΦ e)
  have hg_surj : Function.Surjective g := Finite.injective_iff_surjective.mp hg
  set e0 : Fin 3 → F := ![1, 0, 0] with he0
  set A₀ := a1Mat (h e0) with hA₀
  set Ac := a1Mat (h (c • e0)) with hAc
  have hA₀g : ∀ y, Φ (fr y) = A₀ *ᵥ g y := by
    intro y
    rw [← a1Pair_eq_mulVec, ← hgh, a1Pair_e0]
  have hAcg : ∀ y, Φ (c • fr y) = Ac *ᵥ g y := by
    intro y
    rw [← a1Pair_eq_mulVec, ← hgh, a1Pair_smul_left, a1Pair_e0]
  have hA₀inj : Function.Injective (A₀ *ᵥ ·) := by
    intro w w' hw
    obtain ⟨y, rfl⟩ := hg_surj w
    obtain ⟨y', rfl⟩ := hg_surj w'
    simp only at hw
    rw [← hA₀g, ← hA₀g] at hw
    rw [hfr_inj (hΦ hw)]
  have hA₀u : IsUnit A₀ := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    exact hA₀inj
  set D := Ac * A₀⁻¹ with hD
  have hDΦ : ∀ r, Φ (c • r) = D *ᵥ Φ r := by
    intro r
    obtain ⟨y, rfl⟩ := hfr_surj r
    rw [hA₀g, hAcg, hD, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := A₀⁻¹) (N := A₀),
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA₀u), Matrix.one_mulVec]
  have hrel : ∀ z x, a1Pair z (h (c • x)) = D *ᵥ a1Pair z (h x) := by
    intro z x
    obtain ⟨y, rfl⟩ := hg_surj z
    rw [← hgh, ← hgh, a1Pair_smul_left, hDΦ]
  have key : ∀ w : Fin 3 → F, ∃ w' : Fin 3 → F,
      ![w' 0 * w' 0, w' 1, w' 2] = D *ᵥ ![w 0 * w 0, w 1, w 2] ∧
      ![w' 1, 0, w' 0] = D *ᵥ ![w 1, 0, w 0] ∧ ![w' 2, w' 0, 0] = D *ᵥ ![w 2, w 0, 0] := by
    intro w
    obtain ⟨x, rfl⟩ := hh_surj w
    refine ⟨h (c • x), ?_, ?_, ?_⟩
    · rw [← a1Pair_e0, ← a1Pair_e0, hrel]
    · rw [← a1Pair_e1, ← a1Pair_e1, hrel]
    · rw [← a1Pair_e2, ← a1Pair_e2, hrel]
  have hmv : ∀ v : Fin 3 → F, ∀ i, (D *ᵥ v) i = D i 0 * v 0 + D i 1 * v 1 + D i 2 * v 2 := by
    intro v i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc]
  obtain ⟨wa, ha0, ha1, ha2⟩ := key ![0, 1, 0]
  obtain ⟨wb, hb0, hb1, hb2⟩ := key ![1, 0, 0]
  obtain ⟨wc, hc0, hc1, hc2⟩ := key ![0, 0, 1]
  have E : ∀ {a b : Fin 3 → F}, a = b → ∀ i, a i = b i := fun h i => congrFun h i
  have a1 := E ha1 1
  have a0 := E ha1 0
  have a'1 := E ha0 1
  have b1 := E hb1 1
  have b0 := E hb1 0
  have b2 := E hb1 2
  have b'0 := E hb0 0
  have b'1 := E hb0 1
  have b'2 := E hb0 2
  have b''0 := E hb2 0
  have b''2 := E hb2 2
  have c'2 := E hc0 2
  have c''0 := E hc2 0
  have c''2 := E hc2 2
  simp only [hmv, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, mul_zero, mul_one, add_zero,
    zero_add] at a1 a0 a'1 b1 b0 b2 b'0 b'1 b'2 b''0 b''2 c'2 c''0 c''2
  have hd10 : D 1 0 = 0 := by linear_combination -a1
  have hd12 : D 1 2 = 0 := by linear_combination -b1
  have hd20 : D 2 0 = 0 := by linear_combination -c''2
  have hd21 : D 2 1 = 0 := by linear_combination -b''2
  have hd02 : D 0 2 = 0 := by linear_combination b'1 - b0 + hd10
  have hd01 : D 0 1 = 0 := by linear_combination b'2 - b''0 + hd20
  have hd00 : D 1 1 = D 0 0 := by linear_combination a0 - a'1
  have hd22 : D 2 2 = D 0 0 := by linear_combination c''0 - c'2
  have hsq : D 0 0 * D 0 0 = D 0 0 := by
    have e : wb 0 = D 0 0 := b2.trans hd22
    calc D 0 0 * D 0 0 = wb 0 * wb 0 := by rw [e]
      _ = D 0 0 := b'0
  have h01 : D 0 0 = 0 ∨ D 0 0 = 1 := by
    have : D 0 0 * (D 0 0 - 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h1)
  have hDs : ∀ v, D *ᵥ v = D 0 0 • v := by
    intro v
    ext i
    rw [hmv]
    fin_cases i <;> simp [hd01, hd02, hd10, hd12, hd20, hd21, hd00, hd22]
  have hdc : ∀ r, Φ (c • r) = Φ (D 0 0 • r) := by
    intro r
    rcases h01 with h0 | h1
    · rw [hDΦ, hDs, h0, zero_smul, zero_smul, map_zero]
    · rw [hDΦ, hDs, h1, one_smul, one_smul]
  have hcr := hΦ (hdc e0)
  have hc' : c = D 0 0 := by
    have := congrFun hcr 0
    simpa [he0] using this
  rcases h01 with h0 | h1
  · exact Or.inl (hc'.trans h0)
  · exact Or.inr (hc'.trans h1)

end CFSG.Quasithin.MS93.S32

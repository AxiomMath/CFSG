module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section


open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Om4Model

abbrev Mt : Type := Matrix (Fin 2) (Fin 2) (ZMod 2)

abbrev OmG : Type := SL(2, ZMod 2) × SL(2, ZMod 2)

@[expose] def omSmul (a : OmG) (X : Mt) : Mt := (a.1 : Mt) * X * (a.2 : Mt)ᵀ

@[expose] def polarDet (X Y : Mt) : ZMod 2 := (X + Y).det + X.det + Y.det

theorem polarDet_comm (X Y : Mt) : polarDet X Y = polarDet Y X := by
  rw [polarDet, polarDet, add_comm X Y]
  ring

theorem omSmul_one (X : Mt) : omSmul 1 X = X := by
  simp [omSmul]

theorem omSmul_mul (a b : OmG) (X : Mt) : omSmul (a * b) X = omSmul a (omSmul b X) := by
  simp [omSmul, Matrix.mul_assoc, Matrix.transpose_mul]

theorem omSmul_add (a : OmG) (X Y : Mt) : omSmul a (X + Y) = omSmul a X + omSmul a Y := by
  simp [omSmul, Matrix.mul_add, Matrix.add_mul]

theorem omSmul_zero (a : OmG) : omSmul a 0 = 0 := by
  simp [omSmul]

theorem det_omSmul (a : OmG) (X : Mt) : (omSmul a X).det = X.det := by
  simp [omSmul, Matrix.det_mul, Matrix.det_transpose, a.1.2, a.2.2]

theorem polarDet_omSmul (a : OmG) (X Y : Mt) : polarDet (omSmul a X) (omSmul a Y) = polarDet X Y := by
  simp [polarDet, ← omSmul_add, det_omSmul]

theorem omSmul_eq_zero_iff (a : OmG) (X : Mt) : omSmul a X = 0 ↔ X = 0 := by
  constructor
  · intro h
    have := congrArg (omSmul a⁻¹) h
    rwa [← omSmul_mul, inv_mul_cancel, omSmul_one, omSmul_zero] at this
  · rintro rfl
    exact omSmul_zero a

theorem add_self_mt (X : Mt) : X + X = 0 := by
  ext i j
  have : ∀ z : ZMod 2, z + z = 0 := by decide
  exact this _

theorem det_eq_one_orbit_aux :
    ∀ X : Mt, X.det ≠ 1 ∨ ∃ y : OmG, ∀ l : OmG, l ^ 3 = 1 → omSmul l X ≠ omSmul y X := by
  decide +kernel

theorem det_eq_one_orbit {X : Mt} (hX : X.det = 1) :
    ∃ y : OmG, ∀ l : OmG, l ^ 3 = 1 → omSmul l X ≠ omSmul y X :=
  (det_eq_one_orbit_aux X).resolve_left (not_not.2 hX)

theorem free_of_sing :
    ∀ X : Mt, X ≠ 0 → X.det = 0 → ∀ l : OmG, l ^ 3 = 1 → omSmul l X = X → l = 1 := by
  decide +kernel

theorem exists_vecMulVec :
    ∀ X : Mt, X ≠ 0 → X.det = 0 →
      ∃ a b : Fin 2 → ZMod 2, a ≠ 0 ∧ b ≠ 0 ∧ X = Matrix.vecMulVec a b := by
  decide +kernel


theorem omSmul_vecMulVec :
    ∀ (A B : SL(2, ZMod 2)) (a b : Fin 2 → ZMod 2),
      omSmul (A, B) (Matrix.vecMulVec a b) = Matrix.vecMulVec (A • a) (B • b) := by
  decide +kernel

theorem polarDet_vecMulVec_eq_zero :
    ∀ a b a' b' : Fin 2 → ZMod 2, a = a' ∨ b = b' →
      polarDet (Matrix.vecMulVec a b) (Matrix.vecMulVec a' b') = 0 := by
  decide +kernel

theorem sl2_words_aux : ∀ (a a' : Fin 2 → ZMod 2) (C : SL(2, ZMod 2)), a = 0 ∨ a' = 0 ∨ a = a' ∨
    ∃ A A' : SL(2, ZMod 2), A • a = a ∧ A' • a' = a' ∧
      C ∈ [1, A, A', A * A', A' * A, A * A' * A] := by
  decide +kernel

theorem det_eq_zero_of_decomp {X : Mt} {P : OmG → Prop}
    (hdec : ∀ y : OmG, ∃ l υ : OmG, l ^ 3 = 1 ∧ P υ ∧ y = l * υ)
    (hfix : ∀ υ, P υ → omSmul υ X = X) : X.det = 0 := by
  by_contra h0
  have h1 : X.det = 1 := by
    have : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
    exact this _ h0
  obtain ⟨y, hy⟩ := det_eq_one_orbit h1
  obtain ⟨l, υ, hl, hυ, rfl⟩ := hdec y
  apply hy l hl
  rw [omSmul_mul, hfix υ hυ]

theorem pred_of_stab {X : Mt} (hX : X ≠ 0) (hdet : X.det = 0) {P : OmG → Prop}
    (hdec : ∀ y : OmG, ∃ l υ : OmG, l ^ 3 = 1 ∧ P υ ∧ y = l * υ)
    (hfix : ∀ υ, P υ → omSmul υ X = X) {s : OmG} (hs : omSmul s X = X) : P s := by
  obtain ⟨l, υ, hl, hυ, rfl⟩ := hdec s
  rw [omSmul_mul, hfix υ hυ] at hs
  have : l = 1 := free_of_sing X hX hdet l hl hs
  rw [this, one_mul]
  exact hυ

theorem left_mem_of_words {J : Subgroup OmG} {a a' : Fin 2 → ZMod 2} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (haa : a ≠ a') (hJ : ∀ A : SL(2, ZMod 2), A • a = a → (A, 1) ∈ J)
    (hJ' : ∀ A : SL(2, ZMod 2), A • a' = a' → (A, 1) ∈ J) (C : SL(2, ZMod 2)) : (C, 1) ∈ J := by
  rcases sl2_words_aux a a' C with h | h | h | h
  · exact absurd h ha
  · exact absurd h ha'
  · exact absurd h haa
  obtain ⟨A, A', hA, hA', hC⟩ := h
  have hm : ∀ x y : SL(2, ZMod 2), (x * y, (1 : SL(2, ZMod 2))) = (x, 1) * (y, 1) := by
    intro x y; simp
  have h1 := hJ A hA
  have h2 := hJ' A' hA'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
  · exact J.one_mem
  · exact h1
  · exact h2
  · rw [hm]; exact J.mul_mem h1 h2
  · rw [hm]; exact J.mul_mem h2 h1
  · rw [hm, hm]; exact J.mul_mem (J.mul_mem h1 h2) h1

theorem right_mem_of_words {J : Subgroup OmG} {b b' : Fin 2 → ZMod 2} (hb : b ≠ 0) (hb' : b' ≠ 0)
    (hbb : b ≠ b') (hJ : ∀ B : SL(2, ZMod 2), B • b = b → (1, B) ∈ J)
    (hJ' : ∀ B : SL(2, ZMod 2), B • b' = b' → (1, B) ∈ J) (C : SL(2, ZMod 2)) : (1, C) ∈ J := by
  rcases sl2_words_aux b b' C with h | h | h | h
  · exact absurd h hb
  · exact absurd h hb'
  · exact absurd h hbb
  obtain ⟨A, A', hA, hA', hC⟩ := h
  have hm : ∀ x y : SL(2, ZMod 2), ((1 : SL(2, ZMod 2)), x * y) = (1, x) * (1, y) := by
    intro x y; simp
  have h1 := hJ A hA
  have h2 := hJ' A' hA'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl
  · exact J.one_mem
  · exact h1
  · exact h2
  · rw [hm]; exact J.mul_mem h1 h2
  · rw [hm]; exact J.mul_mem h2 h1
  · rw [hm, hm]; exact J.mul_mem (J.mul_mem h1 h2) h1

theorem generation {X₁ X₂ : Mt} (h1 : X₁ ≠ 0) (h2 : X₂ ≠ 0) (d1 : X₁.det = 0) (d2 : X₂.det = 0)
    (hp : polarDet X₁ X₂ ≠ 0) {J : Subgroup OmG}
    (hJ1 : ∀ s : OmG, omSmul s X₁ = X₁ → s ∈ J) (hJ2 : ∀ s : OmG, omSmul s X₂ = X₂ → s ∈ J) :
    J = ⊤ := by
  obtain ⟨a, b, ha, hb, rfl⟩ := exists_vecMulVec X₁ h1 d1
  obtain ⟨a', b', ha', hb', rfl⟩ := exists_vecMulVec X₂ h2 d2
  have haa : a ≠ a' := fun h => hp (polarDet_vecMulVec_eq_zero a b a' b' (Or.inl h))
  have hbb : b ≠ b' := fun h => hp (polarDet_vecMulVec_eq_zero a b a' b' (Or.inr h))
  rw [eq_top_iff]
  rintro ⟨y1, y2⟩ -
  have hL := left_mem_of_words (J := J) ha ha' haa
    (fun A hA => hJ1 _ (by rw [omSmul_vecMulVec, hA, one_smul]))
    (fun A hA => hJ2 _ (by rw [omSmul_vecMulVec, hA, one_smul])) y1
  have hR := right_mem_of_words (J := J) hb hb' hbb
    (fun B hB => hJ1 _ (by rw [omSmul_vecMulVec, hB, one_smul]))
    (fun B hB => hJ2 _ (by rw [omSmul_vecMulVec, hB, one_smul])) y2
  have := J.mul_mem hL hR
  simpa using this

end CFSG.Quasithin.Om4Model


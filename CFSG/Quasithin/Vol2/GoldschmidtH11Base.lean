module

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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
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

open scoped MatrixGroups Polynomial

namespace CFSG.Quasithin.H11

section Unitriangular

variable {F : Type} [Field F]

@[expose] def uSL (c : F) : SL(2, F) := ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def lSL (c : F) : SL(2, F) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

theorem coe_uSL (c : F) : ((uSL c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := rfl

theorem coe_lSL (c : F) : ((lSL c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![1, 0; c, 1] := rfl

theorem uSL_zero : uSL (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uSL]

theorem uSL_injective : Function.Injective (uSL : F → SL(2, F)) := by
  intro c d h
  have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [coe_uSL] using this

theorem map_uSL (ψ : F ≃+* F) (c : F) :
    Matrix.SpecialLinearGroup.map ψ.toRingHom (uSL c) = uSL (ψ c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uSL, RingHom.mapMatrix_apply]

theorem map_lSL (ψ : F ≃+* F) (c : F) :
    Matrix.SpecialLinearGroup.map ψ.toRingHom (lSL c) = lSL (ψ c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lSL, RingHom.mapMatrix_apply]

end Unitriangular

section Quadratic

variable {F : Type} [Field F] [Finite F] [CharP F 2] (a : ℕ)

@[expose] noncomputable def sg : F →+* F := iterateFrobenius F 2 a

omit [Finite F] in
theorem sg_apply (x : F) : sg a x = x ^ 2 ^ a := rfl

theorem sg_sg (h : Nat.card F = 2 ^ (2 * a)) (x : F) : sg a (sg a x) = x := by
  have := Fintype.ofFinite F
  have h1 := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, h] at h1
  rw [sg_apply, sg_apply, ← pow_mul, ← pow_add, ← two_mul]
  exact h1

@[expose] noncomputable def Kf : Subfield F := RingHom.eqLocusField (sg a) (RingHom.id F)

omit [Finite F] in
theorem mem_Kf {x : F} : x ∈ (Kf a : Subfield F) ↔ sg a x = x := Iff.rfl

omit [Finite F] in
theorem eq_one_of_mul_self_eq_one {k : F} (h : k * k = 1) : k = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have : (k - 1) ^ 2 = 0 := by linear_combination h + (1 - k) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

omit [Finite F] in
theorem card_Kf_le (ha : 0 < a) : Nat.card ((Kf a : Subfield F) : Set F) ≤ 2 ^ a := by
  classical
  have hp : 1 < 2 ^ a := Nat.one_lt_two_pow ha.ne'
  have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq F hp
  have hne : (Polynomial.X ^ 2 ^ a - Polynomial.X : F[X]) ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hdeg; omega
  have hsub : ((Kf a : Subfield F) : Set F) ⊆
      ↑(Polynomial.X ^ 2 ^ a - Polynomial.X : F[X]).roots.toFinset := by
    intro x hx
    have hx' : x ^ 2 ^ a = x := hx
    simp [Polynomial.mem_roots hne, hx']
  calc Nat.card ((Kf a : Subfield F) : Set F) = ((Kf a : Subfield F) : Set F).ncard :=
        Nat.card_coe_set_eq _
    _ ≤ (↑(Polynomial.X ^ 2 ^ a - Polynomial.X : F[X]).roots.toFinset : Set F).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Polynomial.X ^ 2 ^ a - Polynomial.X : F[X]).roots.toFinset.card :=
        Set.ncard_coe_finset _
    _ ≤ Multiset.card (Polynomial.X ^ 2 ^ a - Polynomial.X : F[X]).roots :=
        Multiset.toFinset_card_le _
    _ ≤ (Polynomial.X ^ 2 ^ a - Polynomial.X : F[X]).natDegree := Polynomial.card_roots' _
    _ = 2 ^ a := hdeg

omit [Finite F] in
theorem exists_sg_ne (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) : ∃ x : F, sg a x ≠ x := by
  by_contra hcon
  have hall : ((Kf a : Subfield F) : Set F) = Set.univ :=
    Set.eq_univ_of_forall fun x => by_contra fun hx => hcon ⟨x, hx⟩
  have h1 := card_Kf_le (F := F) a ha
  rw [hall, Nat.card_univ, h] at h1
  have : 2 ^ a < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

theorem sg_add_self_mem (h : Nat.card F = 2 ^ (2 * a)) (x : F) :
    x + sg a x ∈ (Kf a : Subfield F) := by
  rw [mem_Kf, map_add, sg_sg a h, add_comm]

theorem exists_trace_one (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) :
    ∃ θ : F, θ + sg a θ = 1 := by
  obtain ⟨x, hx⟩ := exists_sg_ne a ha h
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have ht : x + sg a x ≠ 0 := by
    intro h0
    apply hx
    linear_combination h0 - x * h2
  have htK : sg a (x + sg a x) = x + sg a x := sg_add_self_mem a h x
  refine ⟨x / (x + sg a x), ?_⟩
  rw [map_div₀, htK, ← add_div, div_self ht]

theorem card_Kf (ha : 0 < a) (h : Nat.card F = 2 ^ (2 * a)) :
    Nat.card ((Kf a : Subfield F) : Set F) = 2 ^ a := by
  refine le_antisymm (card_Kf_le a ha) ?_
  obtain ⟨θ, hθ⟩ := exists_trace_one a ha h
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hsurj : Function.Surjective (fun p : ((Kf a : Subfield F) : Set F) ×
      ((Kf a : Subfield F) : Set F) => (p.1 : F) + p.2 * θ) := by
    intro x
    have hb : x + sg a x ∈ (Kf a : Subfield F) := sg_add_self_mem a h x
    have hc : x + (x + sg a x) * θ ∈ (Kf a : Subfield F) := by
      rw [mem_Kf, map_add, map_mul, (mem_Kf a).mp hb]
      linear_combination (x + sg a x) * hθ + (sg a x - (x + sg a x) * θ) * h2
    exact ⟨⟨⟨_, hc⟩, ⟨_, hb⟩⟩, by
      show x + (x + sg a x) * θ + (x + sg a x) * θ = x
      linear_combination ((x + sg a x) * θ) * h2⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, h] at hle
  by_contra hlt
  have hlt' : Nat.card ((Kf a : Subfield F) : Set F) < 2 ^ a := not_le.mp hlt
  have : Nat.card ((Kf a : Subfield F) : Set F) * Nat.card ((Kf a : Subfield F) : Set F) <
      2 ^ a * 2 ^ a := Nat.mul_self_lt_mul_self hlt'
  have h3 : 2 ^ (2 * a) = 2 ^ a * 2 ^ a := by rw [← pow_add, two_mul]
  omega

end Quadratic

end CFSG.Quasithin.H11

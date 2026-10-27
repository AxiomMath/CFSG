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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.InformationTheory.Hamming
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SteinbergCB

open Module

theorem zmod_two_vec_add_self {n : ℕ} (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h (x i)

theorem card_coord_ne_zero {n : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2)) [Fintype U]
    (i : Fin n) {u₀ : Fin n → ZMod 2} (hu₀ : u₀ ∈ U) (hi : u₀ i ≠ 0) :
    2 * Fintype.card {u : U // (u : Fin n → ZMod 2) i ≠ 0} = Fintype.card U := by
  classical
  have h1 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hu₀i : u₀ i = 1 := h1 _ hi
  let e : {u : U // (u : Fin n → ZMod 2) i ≠ 0} ≃ {u : U // ¬ (u : Fin n → ZMod 2) i ≠ 0} :=
    { toFun := fun u => ⟨⟨u.1 + u₀, U.add_mem u.1.2 hu₀⟩, by
        have := h1 _ u.2
        simp only [Pi.add_apply, this, hu₀i, not_not]
        decide⟩
      invFun := fun u => ⟨⟨u.1 + u₀, U.add_mem u.1.2 hu₀⟩, by
        have h0 : (u.1 : Fin n → ZMod 2) i = 0 := not_not.1 u.2
        simp only [Pi.add_apply, h0, hu₀i]
        decide⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Subtype.ext
        change (u.1 : Fin n → ZMod 2) + u₀ + u₀ = u.1
        rw [add_assoc, zmod_two_vec_add_self, add_zero]
      right_inv := fun u => by
        apply Subtype.ext
        apply Subtype.ext
        change (u.1 : Fin n → ZMod 2) + u₀ + u₀ = u.1
        rw [add_assoc, zmod_two_vec_add_self, add_zero] }
  have h2 := Fintype.card_subtype_compl (fun u : U => (u : Fin n → ZMod 2) i ≠ 0)
  have h3 : Fintype.card {u : U // (u : Fin n → ZMod 2) i ≠ 0} ≤ Fintype.card U :=
    Fintype.card_subtype_le _
  rw [← Fintype.card_congr e] at h2
  omega

theorem support_card_mul_eq {n w : ℕ} (U : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hw : ∀ u ∈ U, u ≠ 0 → hammingNorm u = w) (hd : 0 < finrank (ZMod 2) U) :
    Nat.card {i : Fin n // ∃ u ∈ U, u i ≠ 0} * 2 ^ (finrank (ZMod 2) U - 1) =
      w * (2 ^ finrank (ZMod 2) U - 1) := by
  classical
  let _ : Fintype U := Fintype.ofFinite U
  have hcardU : Fintype.card U = 2 ^ finrank (ZMod 2) U := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hpow : 2 ^ finrank (ZMod 2) U = 2 * 2 ^ (finrank (ZMod 2) U - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hsum : ∑ u : U, hammingNorm (u : Fin n → ZMod 2) =
      ∑ i : Fin n, Fintype.card {u : U // (u : Fin n → ZMod 2) i ≠ 0} := by
    simp only [hammingNorm, Finset.card_filter, Fintype.card_subtype]
    exact Finset.sum_comm
  have hleft : ∑ u : U, hammingNorm (u : Fin n → ZMod 2) = w * (2 ^ finrank (ZMod 2) U - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : U))]
    have h0 : hammingNorm ((0 : U) : Fin n → ZMod 2) = 0 := by simp
    have hne : ∀ u ∈ Finset.univ.erase (0 : U), hammingNorm (u : Fin n → ZMod 2) = w :=
      fun u hu => hw u.1 u.2 fun h => (Finset.mem_erase.1 hu).1 (Subtype.ext h)
    rw [h0, add_zero, Finset.sum_congr rfl hne, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardU, smul_eq_mul, mul_comm]
  have hright : ∀ i : Fin n, Fintype.card {u : U // (u : Fin n → ZMod 2) i ≠ 0} =
      if ∃ u ∈ U, u i ≠ 0 then 2 ^ (finrank (ZMod 2) U - 1) else 0 := by
    intro i
    split_ifs with h
    · obtain ⟨u₀, hu₀, hi⟩ := h
      have := card_coord_ne_zero U i hu₀ hi
      rw [hcardU, hpow] at this
      omega
    · rw [Fintype.card_eq_zero_iff]
      refine ⟨fun u => h ⟨u.1, u.1.2, u.2⟩⟩
  rw [hleft, Finset.sum_congr rfl fun i _ => hright i, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, smul_eq_mul] at hsum
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hsum]

@[expose] def weightFourVecA : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 0, 0, 0]

@[expose] def weightFourVecB : Fin 7 → ZMod 2 := ![0, 0, 1, 1, 1, 1, 0]

@[expose] def weightFourVecC : Fin 7 → ZMod 2 := ![1, 0, 1, 0, 1, 0, 1]

theorem weightFour_combination : ∀ a b c : ZMod 2,
    a • weightFourVecA + b • weightFourVecB + c • weightFourVecC ≠ 0 →
      hammingNorm (a • weightFourVecA + b • weightFourVecB + c • weightFourVecC) = 4 := by
  decide +kernel

theorem weightFour_linearIndependent :
    LinearIndependent (ZMod 2) ![weightFourVecA, weightFourVecB, weightFourVecC] := by
  refine Fintype.linearIndependent_iff.2 ?_
  decide +kernel

theorem range_weightFour : Set.range ![weightFourVecA, weightFourVecB, weightFourVecC] =
    {weightFourVecA, weightFourVecB, weightFourVecC} := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty,
    Set.union_empty, Set.singleton_union, Set.singleton_union]

theorem A7_binary_constant_weight_support_equation :
    (∀ n w d : ℕ, 0 < n → 0 < w → 0 < d → ∀ U : Submodule (ZMod 2) (Fin n → ZMod 2),
      finrank (ZMod 2) U = d → (∀ u ∈ U, u ≠ 0 → hammingNorm u = w) →
        Nat.card {i : Fin n // ∃ u ∈ U, u i ≠ 0} * 2 ^ (d - 1) = w * (2 ^ d - 1)) ∧
    (∀ U : Submodule (ZMod 2) (Fin 7 → ZMod 2), (∀ u ∈ U, u ≠ 0 → hammingNorm u = 4) →
      finrank (ZMod 2) U ≤ 3) ∧
    finrank (ZMod 2) (Submodule.span (ZMod 2) {weightFourVecA, weightFourVecB, weightFourVecC}) =
      3 ∧
    ∀ u ∈ Submodule.span (ZMod 2) {weightFourVecA, weightFourVecB, weightFourVecC}, u ≠ 0 →
      hammingNorm u = 4 := by
  refine ⟨fun n w d _ _ hd U hUd hw => hUd ▸ support_card_mul_eq U hw (hUd ▸ hd), ?_, ?_, ?_⟩
  · intro U hw
    by_contra hlt
    push Not at hlt
    have h := support_card_mul_eq U hw (by omega)
    obtain ⟨e, he⟩ : ∃ e, finrank (ZMod 2) U = e + 4 := ⟨finrank (ZMod 2) U - 4, by omega⟩
    rw [he, show e + 4 - 1 = e + 3 by omega, pow_add, pow_add, show (2 : ℕ) ^ 3 = 8 by norm_num,
      show (2 : ℕ) ^ 4 = 16 by norm_num] at h
    have hpos : 0 < 2 ^ e := pow_pos (by norm_num) e
    generalize 2 ^ e = X at h hpos
    rw [← mul_assoc] at h
    generalize Nat.card {i : Fin 7 // ∃ u ∈ U, u i ≠ 0} * X = Y at h
    omega
  · rw [← range_weightFour, finrank_span_eq_card weightFour_linearIndependent, Fintype.card_fin]
  · intro u hu hu0
    obtain ⟨a, z, hz, rfl⟩ := Submodule.mem_span_insert.1 hu
    obtain ⟨b, y, hy, rfl⟩ := Submodule.mem_span_insert.1 hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [← add_assoc] at hu0 ⊢
    exact weightFour_combination a b c hu0

end CFSG.Quasithin.SteinbergCB

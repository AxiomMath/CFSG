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
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.L319.S66

theorem card_fixed_of_involution_four {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4)
    (γ : Matrix.SpecialLinearGroup (Fin 2) K) (h2 : γ ^ 2 = 1) (h1 : γ ≠ 1) :
    Nat.card {v : Fin 2 → K // Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) v = v} = 4 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hchar : ringChar K = 2 := FiniteField.even_card_iff_char_two.mpr (by omega)
  have h2K : (2 : K) = 0 := by
    have h := (ringChar.spec K 2).mpr (by simp [hchar])
    exact_mod_cast h
  have hxx : ∀ x : Fin 2 → K, x + x = 0 := by
    intro x
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    rw [← two_mul, h2K, zero_mul]
  have hγ2 : (γ : Matrix (Fin 2) (Fin 2) K) * (γ : Matrix (Fin 2) (Fin 2) K) = 1 := by
    rw [← pow_two, ← Matrix.SpecialLinearGroup.coe_pow, h2, Matrix.SpecialLinearGroup.coe_one]
  have hγv : ∀ v : Fin 2 → K,
      Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K)
        (Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hγ2, Matrix.one_mulVec]
  have hγ1ne : (γ : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro hγ1
    apply h1
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    exact congrFun (congrFun hγ1 i) j
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin 2) (Fin 2) K, N = (γ : Matrix (Fin 2) (Fin 2) K) - 1 :=
    ⟨_, rfl⟩
  have hNv : ∀ x : Fin 2 → K,
      Matrix.mulVec N x = Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) x - x := by
    intro x
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hfix : ∀ v : Fin 2 → K,
      Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) v = v ↔ Matrix.mulVec N v = 0 := by
    intro v
    rw [hNv, sub_eq_zero]
  have hsq : ∀ v : Fin 2 → K, Matrix.mulVec N (Matrix.mulVec N v) = 0 := by
    intro v
    rw [hNv (Matrix.mulVec N v), hNv v, Matrix.mulVec_sub, hγv v]
    have e : ∀ a b : Fin 2 → K, a - b - (b - a) = (a + a) - (b + b) := fun a b => by abel
    rw [e, hxx, hxx, sub_self]
  have hNne : ∃ v : Fin 2 → K, Matrix.mulVec N v ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hN0 : N = 0 := Matrix.ext_of_mulVec_single (fun i => by rw [hcon, Matrix.zero_mulVec])
    apply hγ1ne
    rw [hN] at hN0
    exact sub_eq_zero.mp hN0
  obtain ⟨f, hf⟩ : ∃ f : (Fin 2 → K) →ₗ[K] (Fin 2 → K), ∀ x, f x = Matrix.mulVec N x :=
    ⟨Matrix.mulVecLin N, fun x => Matrix.mulVecLin_apply N x⟩
  have hker : ∀ v : Fin 2 → K,
      v ∈ LinearMap.ker f ↔ Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) v = v := by
    intro v
    rw [LinearMap.mem_ker, hf, hfix v]
  have hcardeq : Nat.card {v : Fin 2 → K // Matrix.mulVec (γ : Matrix (Fin 2) (Fin 2) K) v = v}
      = Nat.card (LinearMap.ker f) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun v => (hker v).symm))
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hsum
  have hpos : 0 < Module.finrank K (LinearMap.ker f) := by
    have hex : ∃ x : LinearMap.ker f, x ≠ 0 := by
      obtain ⟨v0, hv0⟩ := hNne
      refine ⟨⟨Matrix.mulVec N v0, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, hf]
        exact hsq v0
      · intro h0
        apply hv0
        simpa using congrArg Subtype.val h0
    exact (Module.finrank_pos_iff_exists_ne_zero (R := K)).mpr hex
  have hfin1 : Module.finrank K (LinearMap.ker f) = 1 := by
    by_contra hne1
    have h2' : Module.finrank K (LinearMap.ker f) = 2 := by omega
    have htop : LinearMap.ker f = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h2', Module.finrank_fin_fun])
    obtain ⟨v0, hv0⟩ := hNne
    apply hv0
    rw [← hf]
    have hmem : v0 ∈ LinearMap.ker f := by
      rw [htop]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp hmem
  rw [hcardeq, Module.natCard_eq_pow_finrank (K := K), hK, hfin1, pow_one]

theorem card_specialLinear_two (K : Type) [Field K] [Fintype K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = Fintype.card K * (Fintype.card K ^ 2 - 1) := by
  rw [Matrix.card_SL_field 2, Fin.prod_univ_two]
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card K = r + 2 := ⟨Fintype.card K - 2, by omega⟩
  rw [hr]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  have e1 : (r + 2) ^ 2 - 1 = r ^ 2 + 4 * r + 3 := Nat.sub_eq_of_eq_add (by ring)
  have e2 : (r + 2) ^ 2 - (r + 2) = r ^ 2 + 3 * r + 2 := Nat.sub_eq_of_eq_add (by ring)
  have e3 : r + 2 - 1 = r + 1 := by omega
  rw [e1, e2, e3]
  exact Nat.div_eq_of_eq_mul_left (by omega) (by ring)

theorem exp_eq_two_of_card_specialLinear {e : ℕ} (h : 2 ^ e * ((2 ^ e) ^ 2 - 1) = 60) : e = 2 := by
  by_contra hne
  rcases Nat.lt_or_ge e 3 with hlt | hge
  · interval_cases e <;> simp_all
  · have h8 : 8 ≤ 2 ^ e := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hge
    have hsq : 64 ≤ (2 ^ e) ^ 2 := by nlinarith
    have h63 : 63 ≤ (2 ^ e) ^ 2 - 1 := by omega
    have hmul : 8 * 63 ≤ 2 ^ e * ((2 ^ e) ^ 2 - 1) := Nat.mul_le_mul h8 h63
    rw [h] at hmul
    omega

end CFSG.Quasithin.H13.L319.S66

end

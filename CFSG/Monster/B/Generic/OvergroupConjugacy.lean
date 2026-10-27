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

namespace CFSG.Monster.B.Generic

open Subgroup
open scoped Pointwise

theorem le_normalCore_of_isSimpleGroup {A : Type*} [Group A] [Finite A] (G H : Subgroup A)
    [IsSimpleGroup G] {n : ℕ} (hn : n.factorial < Nat.card G) (hH : H.index ≤ n) :
    G ≤ H.normalCore := by
  let φ : G →* Equiv.Perm (A ⧸ H) := (MulAction.toPermHom A (A ⧸ H)).comp G.subtype
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with h | h
  · have hle := Nat.card_le_card_of_injective φ ((MonoidHom.ker_eq_bot_iff φ).mp h)
    rw [Nat.card_perm, ← index_eq_card] at hle
    have := Nat.factorial_le hH
    omega
  · intro g hg
    rw [normalCore_eq_ker]
    have hg' : (⟨g, hg⟩ : G) ∈ φ.ker := h ▸ mem_top _
    exact hg'

theorem small_index_simple_overgroup_conjugacy {A : Type*} [Group A] [Finite A]
    (G : Subgroup A) (hG : IsSimpleGroup G) (hcard : 720 < Nat.card G)
    (hindex : G.index = 2 ∨ G.index = 6) :
    G.Normal ∧ (∀ H : Subgroup A, Nat.card H = 2 * Nat.card G → G ≤ H) ∧
      ∀ H J : Subgroup A, Nat.card H = 2 * Nat.card G → Nat.card J = 2 * Nat.card G →
        ∃ a : A, MulAut.conj a • H = J := by
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hGcore : G ≤ G.normalCore :=
    le_normalCore_of_isSimpleGroup G G (n := 6) (by simpa [Nat.factorial] using hcard)
      (by omega)
  have hGn : G.Normal := by
    rw [← le_antisymm (normalCore_le G) hGcore]
    exact normalCore_normal G
  have hHi : ∀ H : Subgroup A, Nat.card H = 2 * Nat.card G → H.index * 2 = G.index := by
    intro H hH
    have h1 := H.card_mul_index
    have h2 := G.card_mul_index
    rw [hH] at h1
    have : Nat.card G * (H.index * 2) = Nat.card G * G.index := by linarith
    exact Nat.eq_of_mul_eq_mul_left hGpos this
  have hle : ∀ H : Subgroup A, Nat.card H = 2 * Nat.card G → G ≤ H := by
    intro H hH
    have := hHi H hH
    exact (le_normalCore_of_isSimpleGroup G H (n := 3)
      (by simp only [Nat.factorial]; omega) (by omega)).trans (normalCore_le H)
  refine ⟨hGn, hle, fun H J hH hJ => ?_⟩
  set π := QuotientGroup.mk' G
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective G
  have hker : π.ker = G := QuotientGroup.ker_mk' G
  have hcomap : ∀ K : Subgroup A, G ≤ K → (K.map π).comap π = K := fun K hK => by
    rw [comap_map_eq, hker, sup_eq_left.mpr hK]
  have hQ : Nat.card (A ⧸ G) = G.index := (index_eq_card G).symm
  have hcard2 : ∀ K : Subgroup A, Nat.card K = 2 * Nat.card G → Nat.card (K.map π) = 2 := by
    intro K hK
    have hi : (K.map π).index = K.index := by
      rw [← index_comap_of_surjective _ hπs, hcomap K (hle K hK)]
    have h1 := (K.map π).card_mul_index
    rw [hi, hQ, ← hHi K hK] at h1
    have hKpos : 0 < K.index := Nat.pos_of_ne_zero (index_ne_zero_of_finite)
    exact Nat.eq_of_mul_eq_mul_left hKpos (by linarith)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card (A ⧸ G)).factorization 2 = 1 := by
    rw [hQ]
    rcases hindex with h | h <;> rw [h]
    · simp [Nat.prime_two.factorization]
    · rw [show (6 : ℕ) = 2 * 3 by rfl, Nat.factorization_mul (by norm_num) (by norm_num),
        Nat.prime_two.factorization, Nat.prime_three.factorization]
      simp
  let P : Sylow 2 (A ⧸ G) := Sylow.ofCard (H.map π) (by rw [hcard2 H hH, hfac, pow_one])
  let R : Sylow 2 (A ⧸ G) := Sylow.ofCard (J.map π) (by rw [hcard2 J hJ, hfac, pow_one])
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq (A ⧸ G) P R
  obtain ⟨a, rfl⟩ := hπs q
  have hqR : MulAut.conj (π a) • H.map π = J.map π := by
    have := congrArg (fun S : Sylow 2 (A ⧸ G) => (S : Subgroup (A ⧸ G))) hq
    simpa [Sylow.coe_subgroup_smul, P, R] using this
  refine ⟨a, (eq_of_le_of_card_ge ?_ ?_).symm⟩
  ·
    intro x hx
    have hx' : π x ∈ MulAut.conj (π a) • H.map π := hqR ▸ mem_map_of_mem π hx
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hx' ⊢
    have : π ((MulAut.conj a)⁻¹ • x) ∈ H.map π := by simpa [MulAut.smul_def] using hx'
    rw [← mem_comap, hcomap H (hle H hH)] at this
    exact this
  · rw [← Nat.card_congr (equivSMul (MulAut.conj a) H).toEquiv, hH, hJ]

end CFSG.Monster.B.Generic

module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSmallAlternating
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

namespace CFSG.Sporadic.Recognition.JankoWong

theorem card_sylow_three_eq_four_of_card_twelve {X : Type*} [Group X] [Finite X]
    (hX : Nat.card X = 12)
    (hodd : ∀ K : Subgroup X, K.Normal → Odd (Nat.card K) → K = ⊥) :
    Nat.card (Sylow 3 X) = 4 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 X))
  have hfac12 : (Nat.factorization 12) 3 = 1 := by
    rw [show 12 = 3 * 4 by norm_num,
      Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
      Nat.prime_three.factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
  have hP : Nat.card (P : Subgroup X) = 3 := by
    have h := P.card_eq_multiplicity
    rw [hX, hfac12] at h
    simpa using h
  have hidx : (P : Subgroup X).index = 4 := by
    have h := (P : Subgroup X).card_mul_index
    rw [hP, hX] at h
    omega
  have hdvd : Nat.card (Sylow 3 X) ∣ 4 := by
    have h := Sylow.card_dvd_index P
    rwa [hidx] at h
  have hle : Nat.card (Sylow 3 X) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hmod : Nat.card (Sylow 3 X) % 3 = 1 := by
    have h := card_sylow_modEq_one 3 X
    simpa [Nat.ModEq] using h
  have hne1 : Nat.card (Sylow 3 X) ≠ 1 := by
    intro h1
    have : Subsingleton (Sylow 3 X) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hnormal : (P : Subgroup X).Normal := Sylow.normal_of_subsingleton P
    have hbot : (P : Subgroup X) = ⊥ := hodd _ hnormal (by rw [hP]; decide)
    have hcard := (Subgroup.eq_bot_iff_card _).mp hbot
    omega
  omega

theorem alternatingGroup_four_involution_mul_cube :
    ∀ a b : alternatingGroup (Fin 4), a ^ 2 = 1 → b ^ 3 = 1 → b ≠ 1 → (a * b) ^ 3 = 1 := by
  decide +kernel

theorem cube_mem_of_card_twelve_quotient {C : Type*} [Group C] [Finite C] (O : Subgroup C)
    [O.Normal] (hX : Nat.card (C ⧸ O) = 12)
    (hodd : ∀ K : Subgroup (C ⧸ O), K.Normal → Odd (Nat.card K) → K = ⊥)
    {i f : C} (hi : i ^ 2 = 1) (hf : f ^ 3 = 1) (hfO : f ∉ O) : (i * f) ^ 3 ∈ O := by
  obtain ⟨e⟩ := CFSG.Glauberman.Dickson.huppert_II_8_17_b_order_twelve_four_sylow_three hX
    (card_sylow_three_eq_four_of_card_twelve hX hodd)
  let φ : C →* alternatingGroup (Fin 4) := e.toMonoidHom.comp (QuotientGroup.mk' O)
  have hφ : ∀ x : C, φ x = 1 ↔ x ∈ O := fun x => by
    simp [φ, QuotientGroup.eq_one_iff]
  have h2 : φ i ^ 2 = 1 := by rw [← map_pow, hi, map_one]
  have h3 : φ f ^ 3 = 1 := by rw [← map_pow, hf, map_one]
  have h1 : φ f ≠ 1 := fun h => hfO ((hφ f).1 h)
  have hcube := alternatingGroup_four_involution_mul_cube (φ i) (φ f) h2 h3 h1
  exact (hφ _).1 (by rw [map_pow, map_mul]; exact hcube)

end CFSG.Sporadic.Recognition.JankoWong

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
public import Mathlib.FieldTheory.Finite.Extension
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.PartOne.AUTSL

section Descent

variable {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m n : Type*}

theorem mem_span_of_map_mem_span (s : Set (Matrix m n K)) (u : Matrix m n K)
    (h : u.map (algebraMap K K') ∈
      Submodule.span K' ((fun a : Matrix m n K => a.map (algebraMap K K')) '' s)) :
    u ∈ Submodule.span K s := by
  obtain ⟨τ, hτ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K K')
    (LinearMap.ker_eq_bot.2 (algebraMap K K').injective)
  have hτι : ∀ x : K, τ (algebraMap K K' x) = x := fun x => by
    have := LinearMap.congr_fun hτ x
    simpa using this
  have hτc : ∀ (x : K) (c : K'), τ (algebraMap K K' x * c) = x * τ c := fun x c => by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have key : ∀ w ∈ Submodule.span K' ((fun a : Matrix m n K => a.map (algebraMap K K')) '' s),
      ∀ c : K', (c • w).map τ ∈ Submodule.span K s := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, rfl⟩ := hw
      intro c
      have : (c • a.map (algebraMap K K')).map τ = τ c • a := by
        ext i j
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
        rw [mul_comm c, hτc, mul_comm]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ha)
    | zero =>
      intro c
      simp
    | add w₁ w₂ _ _ h₁ h₂ =>
      intro c
      have : (c • (w₁ + w₂)).map τ = (c • w₁).map τ + (c • w₂).map τ := by
        ext i j
        simp
      rw [this]
      exact Submodule.add_mem _ (h₁ c) (h₂ c)
    | smul d w _ h' =>
      intro c
      have : (c • (d • w)).map τ = ((c * d) • w).map τ := by
        rw [smul_smul]
      rw [this]
      exact h' (c * d)
  have h1 := key _ h 1
  have : ((1 : K') • u.map (algebraMap K K')).map τ = u := by
    ext i j
    simp [hτι]
  rwa [this] at h1

end Descent

section Frobenius

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem exists_ringEquiv_eq_pow_two (σ : K ≃+* K) : ∃ j : ℕ, ∀ x : K, σ x = x ^ 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let g : K ≃ₐ[ZMod 2] K := AlgEquiv.ofRingEquiv (f := σ) fun x =>
    congrArg (fun f : ZMod 2 →+* K => f x)
      (Subsingleton.elim (σ.toRingHom.comp (algebraMap (ZMod 2) K)) (algebraMap (ZMod 2) K))
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod 2) 2 K g
  refine ⟨i, fun x => ?_⟩
  have := hi x
  rw [Nat.card_zmod] at this
  exact this

end Frobenius

section Extension

theorem exists_finite_extension_five (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : Finite K') (_ : CharP K' 2) (ζ : K'),
      IsPrimitiveRoot ζ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero 4 := ⟨by norm_num⟩
  let K' := FiniteField.Extension K 2 4
  have hfin : Finite K' := inferInstance
  have hmod : Module.Finite K K' := Module.Finite.of_finite
  have hrank : Module.finrank K K' = 4 := FiniteField.finrank_extension K 2 4
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hcardK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hcardK' : Nat.card K' = 16 ^ (f : ℕ) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := K'), hrank, hcardK, ← pow_mul,
      mul_comm, pow_mul]
    norm_num
  have hmod5 : 16 ^ (f : ℕ) % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h5 : 5 ∣ Nat.card K'ˣ := by
    rw [Nat.card_units, hcardK']
    omega
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hprim : IsPrimitiveRoot x 5 := hx ▸ IsPrimitiveRoot.orderOf x
  have hchar : CharP K' 2 := charP_of_injective_algebraMap (algebraMap K K').injective 2
  refine ⟨K', inferInstance, inferInstance, hfin, hchar, (x : K'), ?_⟩
  exact IsPrimitiveRoot.coe_units_iff.2 hprim

end Extension

end CFSG.RankThree.PartOne.AUTSL

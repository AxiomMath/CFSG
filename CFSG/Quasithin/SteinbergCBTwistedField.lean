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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

public section

namespace CFSG.Quasithin.SteinbergCB

variable {F : Type*} [Field F]

@[expose] def frobFixed (σ : F →+* F) : Subfield F := RingHom.eqLocusField σ (RingHom.id F)

theorem mem_frobFixed {σ : F →+* F} {x : F} : x ∈ frobFixed σ ↔ σ x = x :=
  RingHom.mem_eqLocusField

theorem frobFixed_apply {σ : F →+* F} (c : frobFixed σ) : σ (c : F) = c :=
  mem_frobFixed.1 c.2

theorem frob_norm_mem {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) (x : F) :
    σ (x * σ x) = x * σ x := by
  rw [map_mul, hinv, mul_comm]

theorem frob_trace_mem {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) (x : F) :
    σ (x + σ x) = x + σ x := by
  rw [map_add, hinv, add_comm]

theorem frob_norm_eq_zero {σ : F →+* F} {x : F} (h : x * σ x = 0) : x = 0 := by
  rcases mul_eq_zero.1 h with h | h
  · exact h
  · exact (map_eq_zero σ).1 h

theorem exists_frob_decomp {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) {ω : F} (hω : σ ω ≠ ω)
    (x : F) : ∃ α β : F, σ α = α ∧ σ β = β ∧ x = α + β * ω := by
  have hne : ω - σ ω ≠ 0 := sub_ne_zero.2 (Ne.symm hω)
  have hβ : σ ((x - σ x) / (ω - σ ω)) = (x - σ x) / (ω - σ ω) := by
    rw [map_div₀, map_sub, map_sub, hinv, hinv, ← neg_sub x (σ x), ← neg_sub ω (σ ω),
      neg_div_neg_eq]
  refine ⟨x - (x - σ x) / (ω - σ ω) * ω, (x - σ x) / (ω - σ ω), ?_, hβ, by ring⟩
  have hmul : (x - σ x) / (ω - σ ω) * (ω - σ ω) = x - σ x := div_mul_cancel₀ _ hne
  rw [map_sub, map_mul, hβ]
  linear_combination hmul

theorem finrank_frobFixed_eq_two {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) {ω : F}
    (hω : σ ω ≠ ω) : Module.finrank (frobFixed σ) F = 2 := by
  have hli : LinearIndependent (frobFixed σ) ![(1 : F), ω] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Subfield.smul_def, Subfield.smul_def, smul_eq_mul, smul_eq_mul, mul_one] at hst
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    · exfalso
      have ht' : (t : F) ≠ 0 := fun h => ht (Subtype.ext h)
      have hωeq : ω = -(s : F) / t := by
        field_simp
        linear_combination hst
      apply hω
      rw [hωeq, map_div₀, map_neg, frobFixed_apply, frobFixed_apply]
  have hsp : ⊤ ≤ Submodule.span (frobFixed σ) (Set.range ![(1 : F), ω]) := by
    intro x _
    obtain ⟨α, β, hα, hβ, rfl⟩ := exists_frob_decomp hinv hω x
    have h1 : (1 : F) ∈ Submodule.span (frobFixed σ) (Set.range ![(1 : F), ω]) :=
      Submodule.subset_span ⟨0, rfl⟩
    have h2 : ω ∈ Submodule.span (frobFixed σ) (Set.range ![(1 : F), ω]) :=
      Submodule.subset_span ⟨1, rfl⟩
    have := Submodule.add_mem _
      (Submodule.smul_mem _ (⟨α, mem_frobFixed.2 hα⟩ : frobFixed σ) h1)
      (Submodule.smul_mem _ (⟨β, mem_frobFixed.2 hβ⟩ : frobFixed σ) h2)
    simpa [Subfield.smul_def] using this
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_fin]

section card

variable [Finite F] {m : ℕ}

theorem two_eq_zero_of_card (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2) : (2 : F) = 0 := by
  have : Fintype F := Fintype.ofFinite F
  have h := FiniteField.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF] at h
  push_cast at h
  exact (pow_eq_zero_iff (by omega)).1 ((pow_eq_zero_iff two_ne_zero).1 h)

theorem charP_two_of_card (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2) : CharP F 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_of_card hm hF)

theorem frob_frob (hF : Nat.card F = (2 ^ m) ^ 2) {σ : F →+* F} (hσ : ∀ x, σ x = x ^ 2 ^ m)
    (x : F) : σ (σ x) = x := by
  have : Fintype F := Fintype.ofFinite F
  rw [hσ, hσ, ← pow_mul, ← sq, ← hF, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem card_frobFixed_le (hm : 1 ≤ m) {σ : F →+* F} (hσ : ∀ x, σ x = x ^ 2 ^ m) :
    Nat.card (frobFixed σ) ≤ 2 ^ m := by
  classical
  have hp1 : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
  set p : Polynomial F := Polynomial.X ^ 2 ^ m - Polynomial.X with hp
  have hp0 : p ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hp1
  have hmem : ∀ x : frobFixed σ, (x : F) ∈ p.roots.toFinset := fun x => by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, hp, Polynomial.IsRoot,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← hσ, frobFixed_apply,
      sub_self]
  calc Nat.card (frobFixed σ) ≤ Nat.card p.roots.toFinset :=
        Nat.card_le_card_of_injective (fun x => ⟨x, hmem x⟩)
          (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
    _ = p.roots.toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ = 2 ^ m := FiniteField.X_pow_card_sub_X_natDegree_eq F hp1

theorem exists_frob_ne (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2) {σ : F →+* F}
    (hσ : ∀ x, σ x = x ^ 2 ^ m) : ∃ ω : F, σ ω ≠ ω := by
  by_contra h
  push Not at h
  have h1 : Nat.card F ≤ Nat.card (frobFixed σ) :=
    Nat.card_le_card_of_injective (fun x => ⟨x, mem_frobFixed.2 (h x)⟩)
      (fun x y hxy => congrArg Subtype.val hxy)
  have h2 := card_frobFixed_le hm hσ
  have h3 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [hF] at h1
  nlinarith

theorem card_frobFixed (hm : 1 ≤ m) (hF : Nat.card F = (2 ^ m) ^ 2) {σ : F →+* F}
    (hσ : ∀ x, σ x = x ^ 2 ^ m) : Nat.card (frobFixed σ) = 2 ^ m := by
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (frobFixed σ) := Fintype.ofFinite _
  obtain ⟨ω, hω⟩ := exists_frob_ne hm hF hσ
  have h := Module.card_eq_pow_finrank (K := frobFixed σ) (V := F)
  rw [finrank_frobFixed_eq_two (frob_frob hF hσ) hω, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, hF] at h
  exact (Nat.pow_left_injective two_ne_zero h).symm

theorem card_frob_norm_one_le {σ : F →+* F} (hσ : ∀ x, σ x = x ^ 2 ^ m) :
    Nat.card {c : F // c * σ c = 1} ≤ 2 ^ m + 1 := by
  classical
  have hmem : ∀ c : {c : F // c * σ c = 1},
      (c : F) ∈ Polynomial.nthRootsFinset (2 ^ m + 1) (1 : F) := fun c => by
    rw [Polynomial.mem_nthRootsFinset (Nat.succ_pos _), pow_succ', ← hσ]
    exact c.2
  calc Nat.card {c : F // c * σ c = 1}
      ≤ Nat.card (Polynomial.nthRootsFinset (2 ^ m + 1) (1 : F)) :=
        Nat.card_le_card_of_injective (fun c => ⟨c, hmem c⟩)
          (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
    _ = (Polynomial.nthRootsFinset (2 ^ m + 1) (1 : F)).card := Nat.card_eq_finsetCard _
    _ ≤ (Polynomial.nthRoots (2 ^ m + 1) (1 : F)).card := Multiset.toFinset_card_le _
    _ ≤ 2 ^ m + 1 := Polynomial.card_nthRoots _ _

end card

end CFSG.Quasithin.SteinbergCB

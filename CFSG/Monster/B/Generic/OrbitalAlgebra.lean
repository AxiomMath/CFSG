module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.Monster.B.Generic

open MulAction Matrix
open scoped Matrix

variable {K Ω : Type*} [Group K] [MulAction K Ω]

noncomputable def orbitalMatrix (O : orbitRel.Quotient K (Ω × Ω)) : Matrix Ω Ω ℝ :=
  Matrix.of fun x y => by
    classical exact if (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) = O then 1 else 0

noncomputable def orbitalValency (O : orbitRel.Quotient K (Ω × Ω)) (x : Ω) : ℕ :=
  Nat.card {y : Ω // (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) = O}

noncomputable def jointEigenspace [Fintype Ω] (p : orbitRel.Quotient K (Ω × Ω) → ℝ) :
    Submodule ℝ (Ω → ℝ) where
  carrier := {v | ∀ O, orbitalMatrix O *ᵥ v = p O • v}
  add_mem' {v w} hv hw O := by
    change orbitalMatrix O *ᵥ (v + w) = p O • (v + w)
    rw [mulVec_add, hv O, hw O, smul_add]
  zero_mem' O := by
    change orbitalMatrix O *ᵥ 0 = p O • 0
    simp
  smul_mem' c v hv O := by
    change orbitalMatrix O *ᵥ (c • v) = p O • (c • v)
    rw [mulVec_smul, hv O, smul_comm]

private lemma mk_smul_pair (g : K) (x y : Ω) :
    (Quotient.mk _ (g • x, g • y) : orbitRel.Quotient K (Ω × Ω)) = Quotient.mk _ (x, y) := by
  rw [← Prod.smul_mk]
  exact orbitRel.Quotient.quotient_smul_eq

private lemma exists_smul_of_mk_eq {x y x' y' : Ω}
    (h : (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) = Quotient.mk _ (x', y')) :
    ∃ g : K, g • x' = x ∧ g • y' = y := by
  obtain ⟨g, hg⟩ := Quotient.exact h
  exact ⟨g, congrArg Prod.fst hg, congrArg Prod.snd hg⟩

theorem orbitalMatrix_apply_of_eq {O : orbitRel.Quotient K (Ω × Ω)} {x y : Ω}
    (h : (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) = O) :
    orbitalMatrix O x y = 1 := by
  simp [orbitalMatrix, h]

theorem orbitalMatrix_apply_of_ne {O : orbitRel.Quotient K (Ω × Ω)} {x y : Ω}
    (h : (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) ≠ O) :
    orbitalMatrix O x y = 0 := by
  simp [orbitalMatrix, h]

theorem orbitalMatrix_apply [DecidableEq (orbitRel.Quotient K (Ω × Ω))]
    (O : orbitRel.Quotient K (Ω × Ω)) (x y : Ω) :
    orbitalMatrix O x y =
      if (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) = O then 1 else 0 := by
  by_cases h : (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) = O
  · simp [h, orbitalMatrix_apply_of_eq h]
  · simp [h, orbitalMatrix_apply_of_ne h]

theorem orbitalMatrix_smul (O : orbitRel.Quotient K (Ω × Ω)) (g : K) (x y : Ω) :
    orbitalMatrix O (g • x) (g • y) = orbitalMatrix O x y := by
  classical
  simp only [orbitalMatrix_apply, mk_smul_pair]

theorem orbitalValency_smul (O : orbitRel.Quotient K (Ω × Ω)) (g : K) (x : Ω) :
    orbitalValency O (g • x) = orbitalValency O x :=
  (Nat.card_congr ((MulAction.toPerm g).subtypeEquiv fun y => by
    rw [MulAction.toPerm_apply, mk_smul_pair])).symm

theorem orbitalValency_eq [IsPretransitive K Ω] (O : orbitRel.Quotient K (Ω × Ω))
    (x y : Ω) : orbitalValency O x = orbitalValency O y := by
  obtain ⟨g, rfl⟩ := exists_smul_eq K x y
  exact (orbitalValency_smul O g x).symm

theorem orbitalValency_diag (x : Ω) :
    orbitalValency (Quotient.mk _ (x, x) : orbitRel.Quotient K (Ω × Ω)) x = 1 := by
  rw [orbitalValency, Nat.card_eq_one_iff_exists]
  refine ⟨⟨x, rfl⟩, fun y => ?_⟩
  obtain ⟨g, h1, h2⟩ := exists_smul_of_mk_eq y.2
  exact Subtype.ext (h2.symm.trans h1)

theorem orbitalValency_pos [IsPretransitive K Ω] [Finite Ω]
    (O : orbitRel.Quotient K (Ω × Ω)) (x₀ : Ω) : 0 < orbitalValency O x₀ := by
  obtain ⟨⟨a, b⟩, rfl⟩ := Quotient.exists_rep O
  rw [orbitalValency_eq _ x₀ a]
  have : Nonempty {y : Ω // (Quotient.mk _ (a, y) : orbitRel.Quotient K (Ω × Ω)) =
      Quotient.mk _ (a, b)} := ⟨⟨b, rfl⟩⟩
  exact Nat.card_pos

theorem sum_orbitalMatrix_row [Fintype Ω] (O : orbitRel.Quotient K (Ω × Ω)) (x : Ω) :
    ∑ y, orbitalMatrix O x y = orbitalValency O x := by
  classical
  simp [orbitalMatrix_apply, Finset.sum_boole, orbitalValency, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

private lemma transpose_eq_of_invariant
    (hsymm : ∀ x y : Ω, (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) =
      Quotient.mk _ (y, x))
    {M : Matrix Ω Ω ℝ} (hM : ∀ (g : K) (x y : Ω), M (g • x) (g • y) = M x y) : Mᵀ = M := by
  ext x y
  obtain ⟨g, hx, hy⟩ := exists_smul_of_mk_eq (hsymm x y)
  rw [transpose_apply, ← hM g y x, hx, hy]

private lemma mul_invariant [Fintype Ω] {M N : Matrix Ω Ω ℝ}
    (hM : ∀ (g : K) (x y : Ω), M (g • x) (g • y) = M x y)
    (hN : ∀ (g : K) (x y : Ω), N (g • x) (g • y) = N x y) :
    ∀ (g : K) (x y : Ω), (M * N) (g • x) (g • y) = (M * N) x y := by
  intro g x y
  simp only [mul_apply]
  calc ∑ z, M (g • x) z * N z (g • y) = ∑ z, M (g • x) (g • z) * N (g • z) (g • y) :=
        (Equiv.sum_comp (MulAction.toPerm g) (fun z => M (g • x) z * N z (g • y))).symm
    _ = ∑ z, M x z * N z y := by simp only [hM, hN]

theorem orbitalMatrix_transpose
    (hsymm : ∀ x y : Ω, (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) =
      Quotient.mk _ (y, x))
    (O : orbitRel.Quotient K (Ω × Ω)) : (orbitalMatrix O)ᵀ = orbitalMatrix O :=
  transpose_eq_of_invariant hsymm (orbitalMatrix_smul O)

theorem orbitalMatrix_mul_comm [Fintype Ω]
    (hsymm : ∀ x y : Ω, (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) =
      Quotient.mk _ (y, x))
    (O O' : orbitRel.Quotient K (Ω × Ω)) :
    orbitalMatrix O * orbitalMatrix O' = orbitalMatrix O' * orbitalMatrix O := by
  have h := transpose_eq_of_invariant hsymm
    (mul_invariant (orbitalMatrix_smul O) (orbitalMatrix_smul O'))
  rw [transpose_mul, orbitalMatrix_transpose hsymm, orbitalMatrix_transpose hsymm] at h
  exact h.symm

private lemma eq_of_projector [Fintype Ω] {E F : Matrix Ω Ω ℝ} (hE : Eᵀ = E) (hE2 : E * E = E)
    (hF : Fᵀ = F) (hF2 : F * F = F) (h : ∀ v, E *ᵥ v = v ↔ F *ᵥ v = v) : E = F := by
  classical
  have hEF : E * F = F := by
    refine ext_of_mulVec_single fun i => ?_
    rw [← mulVec_mulVec]
    exact (h _).2 (by rw [mulVec_mulVec, hF2])
  have hFE : F * E = E := by
    refine ext_of_mulVec_single fun i => ?_
    rw [← mulVec_mulVec]
    exact (h _).1 (by rw [mulVec_mulVec, hE2])
  calc E = Eᵀ := hE.symm
    _ = (F * E)ᵀ := by rw [hFE]
    _ = Eᵀ * Fᵀ := transpose_mul _ _
    _ = E * F := by rw [hE, hF]
    _ = F := hEF

private lemma mem_jointEigenspace [Fintype Ω] {p : orbitRel.Quotient K (Ω × Ω) → ℝ}
    {v : Ω → ℝ} : v ∈ jointEigenspace p ↔ ∀ O, orbitalMatrix O *ᵥ v = p O • v :=
  Iff.rfl

private lemma mulVec_comp_smul [Fintype Ω] {M : Matrix Ω Ω ℝ}
    (hM : ∀ (g : K) (x y : Ω), M (g • x) (g • y) = M x y) (g : K) (v : Ω → ℝ) :
    M *ᵥ (fun z => v (g • z)) = fun x => (M *ᵥ v) (g • x) := by
  ext x
  simp only [mulVec, dotProduct]
  calc ∑ z, M x z * v (g • z) = ∑ z, M (g • x) (g • z) * v (g • z) := by simp only [hM]
    _ = ∑ z, M (g • x) z * v z :=
        Equiv.sum_comp (MulAction.toPerm g) (fun z => M (g • x) z * v z)

private lemma comp_smul_mem_jointEigenspace [Fintype Ω] {p : orbitRel.Quotient K (Ω × Ω) → ℝ}
    {v : Ω → ℝ} (hv : v ∈ jointEigenspace p) (g : K) :
    (fun z => v (g • z)) ∈ jointEigenspace p := by
  rw [mem_jointEigenspace] at hv ⊢
  intro O
  rw [mulVec_comp_smul (orbitalMatrix_smul O), hv O]
  rfl

private lemma submatrix_fixed_iff [Fintype Ω] {E : Matrix Ω Ω ℝ} {W : Submodule ℝ (Ω → ℝ)}
    (hEW : ∀ v, v ∈ W ↔ E *ᵥ v = v) (σ : Equiv.Perm Ω) (hW : ∀ v ∈ W, v ∘ σ ∈ W)
    (hW' : ∀ v ∈ W, v ∘ σ.symm ∈ W) (v : Ω → ℝ) :
    E.submatrix σ σ *ᵥ v = v ↔ E *ᵥ v = v := by
  rw [submatrix_mulVec_equiv, ← hEW]
  constructor
  · intro h
    have hmem : v ∘ σ.symm ∈ W := by
      rw [hEW]
      calc E *ᵥ (v ∘ σ.symm) = ((E *ᵥ (v ∘ σ.symm)) ∘ σ) ∘ σ.symm := by ext; simp
        _ = v ∘ σ.symm := by rw [h]
    simpa [Function.comp_def] using hW _ hmem
  · intro hv
    rw [(hEW _).1 (hW' v hv)]
    ext; simp

private lemma projector_invariant [Fintype Ω] {p : orbitRel.Quotient K (Ω × Ω) → ℝ}
    {E : Matrix Ω Ω ℝ} (hE : Eᵀ = E) (hE2 : E * E = E)
    (hEW : ∀ v, v ∈ jointEigenspace p ↔ E *ᵥ v = v) :
    ∀ (g : K) (x y : Ω), E (g • x) (g • y) = E x y := by
  intro g x y
  have key : E.submatrix (MulAction.toPerm g) (MulAction.toPerm g) = E := by
    refine eq_of_projector (by rw [transpose_submatrix, hE]) (by rw [submatrix_mul_equiv, hE2])
      hE hE2 fun v => submatrix_fixed_iff hEW (MulAction.toPerm g)
        (fun v hv => comp_smul_mem_jointEigenspace hv g)
        (fun v hv => comp_smul_mem_jointEigenspace hv g⁻¹) v
  exact congrFun (congrFun key x) y

private lemma trace_eq_finrank [Fintype Ω] {E : Matrix Ω Ω ℝ} {W : Submodule ℝ (Ω → ℝ)}
    (hE2 : E * E = E) (hEW : ∀ v, v ∈ W ↔ E *ᵥ v = v) :
    E.trace = Module.finrank ℝ W := by
  classical
  have hP : LinearMap.IsProj W (Matrix.toLin' E) := by
    constructor
    · intro x
      rw [hEW, toLin'_apply, mulVec_mulVec, hE2]
    · intro x hx
      rw [toLin'_apply]
      exact (hEW x).1 hx
  rw [← Matrix.trace_toLin'_eq, hP.trace]

private lemma orbitalMatrix_mul_projector [Fintype Ω] {p : orbitRel.Quotient K (Ω × Ω) → ℝ}
    {E : Matrix Ω Ω ℝ} (hE2 : E * E = E) (hEW : ∀ v, v ∈ jointEigenspace p ↔ E *ᵥ v = v)
    (O : orbitRel.Quotient K (Ω × Ω)) : orbitalMatrix O * E = p O • E := by
  classical
  refine ext_of_mulVec_single fun i => ?_
  rw [← mulVec_mulVec, smul_mulVec]
  exact mem_jointEigenspace.1 ((hEW _).2 (by rw [mulVec_mulVec, hE2])) O

private lemma trace_mul_orbitalMatrix [Fintype Ω] [IsPretransitive K Ω]
    (hsymm : ∀ x y : Ω, (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) =
      Quotient.mk _ (y, x))
    {E : Matrix Ω Ω ℝ} (hE : ∀ (g : K) (x y : Ω), E (g • x) (g • y) = E x y) (a b x₀ : Ω) :
    (E * orbitalMatrix (Quotient.mk _ (a, b) : orbitRel.Quotient K (Ω × Ω))).trace =
      E a b * (Fintype.card Ω *
        orbitalValency (Quotient.mk _ (a, b) : orbitRel.Quotient K (Ω × Ω)) x₀) := by
  set O : orbitRel.Quotient K (Ω × Ω) := Quotient.mk _ (a, b)
  have key : ∀ x y, E x y * orbitalMatrix O y x = E a b * orbitalMatrix O x y := by
    intro x y
    rw [← transpose_apply (orbitalMatrix O) x y, orbitalMatrix_transpose hsymm]
    by_cases h : (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) = O
    · obtain ⟨g, rfl, rfl⟩ := exists_smul_of_mk_eq h
      rw [hE]
    · rw [orbitalMatrix_apply_of_ne h, mul_zero, mul_zero]
  calc (E * orbitalMatrix O).trace = ∑ x, ∑ y, E x y * orbitalMatrix O y x := by
        simp only [trace, diag, mul_apply]
    _ = ∑ x, E a b * (orbitalValency O x₀ : ℝ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [key, ← Finset.mul_sum, sum_orbitalMatrix_row, orbitalValency_eq O x x₀]
    _ = E a b * (Fintype.card Ω * orbitalValency O x₀) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

private lemma exists_projector [Fintype Ω] (W : Submodule ℝ (Ω → ℝ)) :
    ∃ E : Matrix Ω Ω ℝ, Eᵀ = E ∧ E * E = E ∧ ∀ v, v ∈ W ↔ E *ᵥ v = v := by
  classical
  let W' : Submodule ℝ (EuclideanSpace ℝ Ω) :=
    W.comap (WithLp.linearEquiv 2 ℝ (Ω → ℝ)).toLinearMap
  obtain ⟨E, hEP⟩ : ∃ E : Matrix Ω Ω ℝ, Matrix.toEuclideanLin E =
      (W'.starProjection : EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ Ω) :=
    Matrix.toEuclideanLin.surjective _
  have hmul : ∀ v : Ω → ℝ, E *ᵥ v = WithLp.ofLp (W'.starProjection (WithLp.toLp 2 v)) :=
    fun v => congrArg (fun f => WithLp.ofLp (f (WithLp.toLp 2 v))) hEP
  refine ⟨E, ?_, ?_, ?_⟩
  · have h : (Matrix.toEuclideanLin E).IsSymmetric := hEP ▸ W'.starProjection_isSymmetric
    rw [Matrix.isSymmetric_toEuclideanLin_iff] at h
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact h.eq
  · refine ext_of_mulVec_single fun i => ?_
    rw [← mulVec_mulVec, hmul, hmul, WithLp.toLp_ofLp]
    congr 1
    exact Submodule.starProjection_eq_self_iff.2 (Submodule.starProjection_apply_mem _ _)
  · intro v
    rw [hmul]
    calc v ∈ W ↔ WithLp.toLp 2 v ∈ W' := Iff.rfl
      _ ↔ W'.starProjection (WithLp.toLp 2 v) = WithLp.toLp 2 v :=
          Submodule.starProjection_eq_self_iff.symm
      _ ↔ WithLp.ofLp (W'.starProjection (WithLp.toLp 2 v)) = v := WithLp.ext_iff 2

theorem symmetric_orbital_positive_spectral_combinations [Fintype Ω] [Nonempty Ω]
    [IsPretransitive K Ω] [Fintype (orbitRel.Quotient K (Ω × Ω))]
    (hsymm : ∀ x y : Ω, (Quotient.mk _ (x, y) : orbitRel.Quotient K (Ω × Ω)) =
      Quotient.mk _ (y, x)) :
    (∀ (O : orbitRel.Quotient K (Ω × Ω)) (x y : Ω), orbitalValency O x = orbitalValency O y) ∧
    (∀ x : Ω, orbitalValency (Quotient.mk _ (x, x) : orbitRel.Quotient K (Ω × Ω)) x = 1) ∧
    (∀ O O' : orbitRel.Quotient K (Ω × Ω),
      orbitalMatrix O * orbitalMatrix O' = orbitalMatrix O' * orbitalMatrix O) ∧
    ∀ (p : orbitRel.Quotient K (Ω × Ω) → ℝ) (x₀ : Ω),
      (∃ v : Ω → ℝ, v ≠ 0 ∧ ∀ O, orbitalMatrix O *ᵥ v = p O • v) →
      (∑ O, (p O / orbitalValency O x₀) • orbitalMatrix O).PosSemidef ∧
      (∃ E : Matrix Ω Ω ℝ, Eᵀ = E ∧ E * E = E ∧ ∀ v, v ∈ jointEigenspace p ↔ E *ᵥ v = v) ∧
      ∀ E : Matrix Ω Ω ℝ, Eᵀ = E → E * E = E →
        (∀ v, v ∈ jointEigenspace p ↔ E *ᵥ v = v) →
        ∑ O, (p O / orbitalValency O x₀) • orbitalMatrix O =
          ((Fintype.card Ω : ℝ) / Module.finrank ℝ (jointEigenspace p)) • E := by
  refine ⟨orbitalValency_eq, orbitalValency_diag, orbitalMatrix_mul_comm hsymm, ?_⟩
  rintro p x₀ ⟨v, hv0, hv⟩
  have hm : 0 < Module.finrank ℝ (jointEigenspace p) := by
    refine Nat.pos_of_ne_zero fun h => hv0 ?_
    exact (Submodule.eq_bot_iff _).1 (Submodule.finrank_eq_zero.1 h) v (mem_jointEigenspace.2 hv)
  have hN : 0 < Fintype.card Ω := Fintype.card_pos
  have hC : ∀ a b, (∑ O, (p O / orbitalValency O x₀) • orbitalMatrix O) a b =
      p (Quotient.mk _ (a, b)) / orbitalValency (Quotient.mk _ (a, b) :
        orbitRel.Quotient K (Ω × Ω)) x₀ := by
    intro a b
    classical
    simp [Matrix.sum_apply, orbitalMatrix_apply]
  have key : ∀ E : Matrix Ω Ω ℝ, Eᵀ = E → E * E = E →
      (∀ v, v ∈ jointEigenspace p ↔ E *ᵥ v = v) →
      ∑ O, (p O / orbitalValency O x₀) • orbitalMatrix O =
        ((Fintype.card Ω : ℝ) / Module.finrank ℝ (jointEigenspace p)) • E := by
    intro E hE hE2 hEW
    have hinv := projector_invariant hE hE2 hEW
    ext a b
    rw [hC a b, Matrix.smul_apply, smul_eq_mul]
    have h1 := trace_mul_orbitalMatrix hsymm hinv a b x₀
    rw [trace_mul_comm, orbitalMatrix_mul_projector hE2 hEW, trace_smul,
      trace_eq_finrank hE2 hEW, smul_eq_mul] at h1
    have hk : (0 : ℝ) < orbitalValency (Quotient.mk _ (a, b) :
        orbitRel.Quotient K (Ω × Ω)) x₀ := by
      exact_mod_cast orbitalValency_pos _ x₀
    have hm' : (0 : ℝ) < Module.finrank ℝ (jointEigenspace p) := by exact_mod_cast hm
    have hN' : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast hN
    field_simp
    linear_combination h1
  obtain ⟨E, hE, hE2, hEW⟩ := exists_projector (jointEigenspace p)
  refine ⟨?_, ⟨E, hE, hE2, hEW⟩, key⟩
  rw [key E hE hE2 hEW]
  refine PosSemidef.smul ?_ (by positivity)
  have hEE : E = Eᴴ * E := by rw [conjTranspose_eq_transpose_of_trivial, hE, hE2]
  rw [hEE]
  exact posSemidef_conjTranspose_mul_self E

end CFSG.Monster.B.Generic

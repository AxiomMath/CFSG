module

public import CFSG.RankThree.SubgroupLists.RationalElements
public import CFSG.RankThree.SubgroupLists2.SpectralBounds
public import CFSG.RankThree.SubgroupLists.CliffordPrime
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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ZPow
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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

namespace CFSG.RankThree.SubgroupLists

open Matrix

variable {K : Type*} [Field K]

theorem commute_of_coe_eq_scalar {s : GL (Fin 3) K} {c : K}
    (hs : (s : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) (g : GL (Fin 3) K) :
    g * s = s * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hs]
  exact (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).symm

theorem mem_center_of_coe_eq_scalar {s : GL (Fin 3) K} {c : K}
    (hs : (s : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) :
    s ∈ Subgroup.center (GL (Fin 3) K) :=
  Subgroup.mem_center_iff.mpr fun g => commute_of_coe_eq_scalar hs g

theorem card_le_three_of_forall_scalar (S : Subgroup (GL (Fin 3) K))
    (hS : ∀ g ∈ S, ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hdet : ∀ g ∈ S, (g : Matrix (Fin 3) (Fin 3) K).det = 1) : Nat.card S ≤ 3 := by
  classical
  set R := (Polynomial.nthRoots 3 (1 : K)).toFinset with hRdef
  have hR : R.card ≤ 3 := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
  have hmem : ∀ g : S, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ∈ R := by
    intro g
    obtain ⟨c, hc⟩ := hS g g.2
    have hd := hdet g g.2
    rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at hd
    rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num), hc,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, hd]
  let f : S → R := fun g => ⟨_, hmem g⟩
  have hf : Function.Injective f := by
    intro g h hgh
    obtain ⟨c, hc⟩ := hS g g.2
    obtain ⟨d, hd⟩ := hS h h.2
    have hcd : c = d := by
      have := congrArg Subtype.val hgh
      simp only [f, hc, hd, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
      exact this
    exact Subtype.ext (Units.ext (by rw [hc, hd, hcd]))
  calc Nat.card S ≤ Nat.card R := Nat.card_le_card_of_injective f hf
    _ = R.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 3 := hR

@[expose] def scalarSL3 (K : Type*) [Field K] : Subgroup (GL (Fin 3) K) :=
  Subgroup.center (GL (Fin 3) K) ⊓ (Matrix.GeneralLinearGroup.det : GL (Fin 3) K →* Kˣ).ker

theorem mem_scalarSL3_of_coe_eq_scalar {s : GL (Fin 3) K} {c : K}
    (hs : (s : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hdet : (s : Matrix (Fin 3) (Fin 3) K).det = 1) : s ∈ scalarSL3 K :=
  ⟨mem_center_of_coe_eq_scalar hs, Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one])⟩

theorem card_scalarSL3_le : Nat.card (scalarSL3 K) ≤ 3 := by
  apply card_le_three_of_forall_scalar
  · intro g hg
    have hgc := hg.1
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hgc
    obtain ⟨μ, rfl⟩ := hgc
    exact ⟨μ, by rw [Matrix.GeneralLinearGroup.coe_scalar]⟩
  · intro g hg
    have h := congrArg Units.val (MonoidHom.mem_ker.mp hg.2)
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h

theorem exists_fixed_vector_of_conj_eq_smul (h3 : (3 : K) ≠ 0) {M P : GL (Fin 3) K} {ω : K}
    (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (hP : (P : Matrix (Fin 3) (Fin 3) K) * M * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω • (M : Matrix (Fin 3) (Fin 3) K))
    (hdet : (M : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ (M : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  classical
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  set X := (M : Matrix (Fin 3) (Fin 3) K) with hX
  set Y := ((M⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hY
  have hconjtr : ∀ g : GL (Fin 3) K,
      ((P * g * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).trace =
        (g : Matrix (Fin 3) (Fin 3) K).trace := fun g =>
    trace_eq_of_isConj (isConj_iff.mpr ⟨P, rfl⟩).symm
  have htr : X.trace = 0 := by
    have h := hconjtr M
    rw [Units.val_mul, Units.val_mul, hP, Matrix.trace_smul, smul_eq_mul] at h
    have : (ω - 1) * X.trace = 0 := by rw [sub_mul, h, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  have hPinv : ((P * M⁻¹ * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ω⁻¹ • Y := by
    have hc : ((P * M * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (ω⁻¹ • Y) = 1 := by
      rw [Units.val_mul, Units.val_mul, hP, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        mul_inv_cancel₀ hω0, one_smul, hX, hY, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hinv : (P * M * P⁻¹)⁻¹ = P * M⁻¹ * P⁻¹ := by group
    rw [← hinv]
    calc (((P * M * P⁻¹)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        = (((P * M * P⁻¹)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (((P * M * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (ω⁻¹ • Y)) := by
          rw [hc, Matrix.mul_one]
      _ = ω⁻¹ • Y := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
            Matrix.one_mul]
  have htrinv : Y.trace = 0 := by
    have h := hconjtr M⁻¹
    rw [hPinv, Matrix.trace_smul, smul_eq_mul] at h
    have hω1' : ω⁻¹ ≠ 1 := fun h' => hω1 (inv_eq_one.mp h')
    have : (ω⁻¹ - 1) * Y.trace = 0 := by rw [sub_mul, h, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1')
  have hcube : X ^ 3 = 1 := by
    have h := cayley_hamilton_sl3 M hdet
    rw [← hX, ← hY, htr, htrinv, zero_smul, zero_smul, sub_zero, zero_add] at h
    exact h
  have hsq : (X ^ 2).trace = 0 := by
    rw [trace_sq_sl3 M hdet, ← hX, ← hY, htr, htrinv]
    ring
  have hsing : (X - 1).det = 0 := by
    by_contra hne
    have hfac : (X - 1) * (X ^ 2 + X + 1) = 0 := by
      have : (X - 1) * (X ^ 2 + X + 1) = X ^ 3 - 1 := by noncomm_ring
      rw [this, hcube, sub_self]
    have hzero : X ^ 2 + X + 1 = 0 := by
      have hu : IsUnit (X - 1) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hne)
      exact (hu.mul_right_eq_zero).mp hfac
    have htr3 := congrArg Matrix.trace hzero
    rw [Matrix.trace_add, Matrix.trace_add, hsq, htr, Matrix.trace_one, Matrix.trace_zero,
      Fintype.card_fin] at htr3
    apply h3
    rw [← htr3]
    push_cast
    ring
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hsing
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv

theorem scalar_of_commute_of_conj_eq_smul {M P : GL (Fin 3) K} {ω : K} (hω1 : ω ≠ 1)
    (hω3 : ω ^ 3 = 1)
    (hP : (P : Matrix (Fin 3) (Fin 3) K) * M * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω • (M : Matrix (Fin 3) (Fin 3) K))
    (hev : ∃ v : Fin 3 → K, v ≠ 0 ∧ ∃ μ : K, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ • v)
    {A : Matrix (Fin 3) (Fin 3) K} (hAM : A * M = M * A) (hAP : A * P = P * A) :
    ∃ c : K, A = Matrix.scalar (Fin 3) c := by
  classical
  have hmq : (M : Matrix (Fin 3) (Fin 3) K) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ω • (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M) := by
    have h := congrArg (HMul.hMul ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hP
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul, Matrix.mul_smul] at h
  obtain ⟨v, hv0, μ, hμ⟩ := hev
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hμ
    apply hv0
    rw [← gl_inv_mulVec_mulVec M v, hμ, Matrix.mulVec_zero]
  let u : Fin 3 → Fin 3 → K := fun j =>
    (((P⁻¹ : GL (Fin 3) K) ^ (j : ℕ) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v
  have hu : ∀ j : ℕ, (M : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((((P⁻¹ : GL (Fin 3) K) ^ j : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (ω ^ j * μ) • ((((P⁻¹ : GL (Fin 3) K) ^ j : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
    intro j
    induction j with
    | zero => simpa using hμ
    | succ j ih =>
      rw [pow_succ', gl_mulVec_mul, Matrix.mulVec_mulVec, hmq, Matrix.smul_mulVec,
        ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, smul_smul, pow_succ]
      ring_nf
  have hu0 : ∀ j, u j ≠ 0 := by
    intro j hj
    apply hv0
    rw [← gl_mulVec_inv_mulVec (P ^ (j : ℕ)) v, ← inv_pow]
    change _ *ᵥ u j = 0
    rw [hj, Matrix.mulVec_zero]
  have hω0 : ω ≠ 0 := by
    rintro rfl
    simp at hω3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have he : Function.Injective fun j : Fin 3 => ω ^ (j : ℕ) * μ := by
    intro i j hij
    have hij' : ω ^ (i : ℕ) = ω ^ (j : ℕ) := mul_right_cancel₀ hμ0 hij
    have hu' : (Units.mk0 ω hω0) ^ (i : ℕ) = (Units.mk0 ω hω0) ^ (j : ℕ) :=
      Units.ext (by simpa using hij')
    rw [pow_eq_pow_iff_modEq, ← orderOf_units, Units.val_mk0, hord] at hu'
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hu' i.2 j.2)
  have hind : LinearIndependent K u :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (M : Matrix (Fin 3) (Fin 3) K))
      (fun j : Fin 3 => ω ^ (j : ℕ) * μ) he u fun j =>
      ⟨Module.End.mem_eigenspace_iff.mpr (by rw [Matrix.toLin'_apply]; exact hu j), hu0 j⟩
  have hspan : Submodule.span K (Set.range u) = ⊤ :=
    hind.span_eq_top_of_card_eq_finrank (by simp)
  obtain ⟨c, hc⟩ : ∃ c : K, A *ᵥ v = c • v := by
    have hmem : A *ᵥ u 0 ∈ Submodule.span K (Set.range u) := hspan ▸ Submodule.mem_top
    obtain ⟨d, hd⟩ := Submodule.mem_span_range_iff_exists_fun K |>.mp hmem
    have hm : (M : Matrix (Fin 3) (Fin 3) K) *ᵥ (A *ᵥ u 0) =
        (ω ^ ((0 : Fin 3) : ℕ) * μ) • (A *ᵥ u 0) := by
      rw [Matrix.mulVec_mulVec, ← hAM, ← Matrix.mulVec_mulVec]
      rw [show (M : Matrix (Fin 3) (Fin 3) K) *ᵥ u 0 = (ω ^ ((0 : Fin 3) : ℕ) * μ) • u 0 from
        hu 0, Matrix.mulVec_smul]
    rw [← hd, Matrix.mulVec_sum] at hm
    simp only [Matrix.mulVec_smul, smul_smul, Finset.smul_sum] at hm
    have hm' : ∑ i, (d i * (ω ^ (i : ℕ) * μ)) • u i =
        ∑ i, ((ω ^ ((0 : Fin 3) : ℕ) * μ) * d i) • u i := by
      rw [← hm]
      exact Finset.sum_congr rfl fun i _ => by rw [show (M : Matrix (Fin 3) (Fin 3) K) *ᵥ u i =
        (ω ^ (i : ℕ) * μ) • u i from hu i, smul_smul]
    have hzero : ∑ i, (d i * (ω ^ (i : ℕ) * μ) - (ω ^ ((0 : Fin 3) : ℕ) * μ) * d i) • u i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, hm', sub_self]
    have hdi := (Fintype.linearIndependent_iff.mp hind) _ hzero
    refine ⟨d 0, ?_⟩
    have hv : u 0 = v := by simp [u]
    rw [← hv, ← hd, Finset.sum_eq_single 0]
    · intro i _ hi0
      have h := hdi i
      have hne : ω ^ (i : ℕ) * μ - ω ^ ((0 : Fin 3) : ℕ) * μ ≠ 0 :=
        sub_ne_zero.mpr fun h' => hi0 (he h')
      have : d i * (ω ^ (i : ℕ) * μ - ω ^ ((0 : Fin 3) : ℕ) * μ) = 0 := by
        linear_combination h
      rw [(mul_eq_zero.mp this).resolve_right hne, zero_smul]
    · simp
  have hcomm : Commute A ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    Commute.units_inv_right hAP
  have hAu : ∀ j, A *ᵥ u j = c • u j := by
    intro j
    have hj : Commute A (((P⁻¹ : GL (Fin 3) K) ^ (j : ℕ) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) := by
      rw [Units.val_pow_eq_pow_val]
      exact hcomm.pow_right _
    change A *ᵥ (_ *ᵥ v) = c • (_ *ᵥ v)
    rw [Matrix.mulVec_mulVec, hj.eq, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]
  refine ⟨c, ?_⟩
  apply Matrix.toLin'.injective
  apply LinearMap.ext_on_range hspan
  intro j
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hAu j, Matrix.scalar_apply]
  ext i
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

theorem card_le_twentyseven_of_scalar_commutators [Finite K] (h3 : (3 : K) ≠ 0)
    (R : Subgroup (GL (Fin 3) K)) (hdet : ∀ x ∈ R, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hcomm : ∀ x ∈ R, ∀ y ∈ R, ∃ c : K,
      ((x * y * x⁻¹ * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c)
    (hcube : ∀ x ∈ R, ∃ c : K,
      ((x ^ 3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c) :
    Nat.card R ≤ 27 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3' : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast h3
  by_cases hab : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  ·
    let κ : R →* GL (Fin 3) K :=
      { toFun := fun x => (x : GL (Fin 3) K) ^ 3
        map_one' := by rw [Subgroup.coe_one, one_pow]
        map_mul' := fun x y => by
          rw [Subgroup.coe_mul, Commute.mul_pow (hab x x.2 y y.2)] }
    have hrange : Nat.card κ.range ≤ 3 := by
      have hle : κ.range ≤ scalarSL3 K := by
        rintro _ ⟨x, rfl⟩
        obtain ⟨c, hc⟩ := hcube x x.2
        refine mem_scalarSL3_of_coe_eq_scalar hc ?_
        exact hdet _ (R.pow_mem x.2 3)
      exact (Subgroup.card_le_of_le hle).trans card_scalarSL3_le
    have hker : Nat.card κ.ker ≤ 9 := by
      have h := card_le_sq_of_elementary (r := 3) h3' (κ.ker.map R.subtype)
        (by
          rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩
          exact hab x x.2 y y.2)
        (by
          rintro _ ⟨x, hx, rfl⟩
          exact hx)
        (by
          rintro _ ⟨x, -, rfl⟩
          exact hdet _ x.2)
      rw [Subgroup.card_map_of_injective R.subtype_injective] at h
      simpa using h
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup κ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange κ).toEquiv] at h1
    rw [h1]
    calc Nat.card κ.range * Nat.card κ.ker ≤ 3 * 9 := Nat.mul_le_mul hrange hker
      _ = 27 := by norm_num
  ·
    push Not at hab
    obtain ⟨b, hb, a, ha, hba⟩ := hab
    obtain ⟨ω, hω⟩ := hcomm b hb a ha
    have hωdet : ω ^ 3 = 1 := by
      have h := hdet _ (R.mul_mem (R.mul_mem (R.mul_mem hb ha) (R.inv_mem hb)) (R.inv_mem ha))
      rwa [hω, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_const] at h
    have hω1 : ω ≠ 1 := by
      rintro rfl
      apply hba
      have h1 : b * a * b⁻¹ * a⁻¹ = 1 := Units.ext (by
        rw [hω, Units.val_one]
        exact map_one _)
      calc b * a = b * a * b⁻¹ * a⁻¹ * (a * b) := by group
        _ = a * b := by rw [h1, one_mul]
    have hP : (b : Matrix (Fin 3) (Fin 3) K) * a * ((b⁻¹ : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ω • (a : Matrix (Fin 3) (Fin 3) K) := by
      have h : ((b * a * b⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((b * a * b⁻¹ * a⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * a := by
        rw [← Units.val_mul, inv_mul_cancel_right]
      rw [Units.val_mul, Units.val_mul] at h
      rw [h, hω, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
        Matrix.one_mul]
    obtain ⟨v, hv0, hv⟩ := exists_fixed_vector_of_conj_eq_smul h3 hω1 hωdet hP (hdet a ha)
    have hev : ∃ v : Fin 3 → K, v ≠ 0 ∧ ∃ μ : K, (a : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ • v :=
      ⟨v, hv0, 1, by rw [one_smul, hv]⟩
    have hcen : ∀ x ∈ R, ∀ y ∈ R, ∀ g : GL (Fin 3) K,
        g * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * g := by
      intro x hx y hy g
      obtain ⟨c, hc⟩ := hcomm x hx y hy
      exact commute_of_coe_eq_scalar hc g
    have hcommap : ∀ z ∈ R, ∀ x ∈ R, ∀ y ∈ R,
        x * y * z * (x * y)⁻¹ * z⁻¹ = (x * z * x⁻¹ * z⁻¹) * (y * z * y⁻¹ * z⁻¹) := by
      intro z hz x hx y hy
      set s := y * z * y⁻¹ * z⁻¹ with hs
      have hs' : y * z * y⁻¹ = s * z := by rw [hs]; group
      calc x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ := by group
        _ = x * (s * z) * x⁻¹ * z⁻¹ := by rw [hs']
        _ = (x * s) * z * x⁻¹ * z⁻¹ := by group
        _ = (s * x) * z * x⁻¹ * z⁻¹ := by rw [hcen y hy z hz x]
        _ = s * (x * z * x⁻¹ * z⁻¹) := by group
        _ = (x * z * x⁻¹ * z⁻¹) * s := by
            rw [hcen y hy z hz (x * z * x⁻¹ * z⁻¹)]
    let θ : R →* GL (Fin 3) K × GL (Fin 3) K :=
      { toFun := fun x => ((x : GL (Fin 3) K) * a * (x : GL (Fin 3) K)⁻¹ * a⁻¹,
          (x : GL (Fin 3) K) * b * (x : GL (Fin 3) K)⁻¹ * b⁻¹)
        map_one' := by simp
        map_mul' := fun x y => by
          simp only [Subgroup.coe_mul, Prod.mk_mul_mk]
          rw [hcommap a ha x x.2 y y.2, hcommap b hb x x.2 y y.2] }
    have hrange : Nat.card θ.range ≤ 9 := by
      have hle : θ.range ≤ (scalarSL3 K).prod (scalarSL3 K) := by
        rintro _ ⟨x, rfl⟩
        constructor
        · obtain ⟨c, hc⟩ := hcomm x x.2 a ha
          exact mem_scalarSL3_of_coe_eq_scalar hc
            (hdet _ (R.mul_mem (R.mul_mem (R.mul_mem x.2 ha) (R.inv_mem x.2)) (R.inv_mem ha)))
        · obtain ⟨c, hc⟩ := hcomm x x.2 b hb
          exact mem_scalarSL3_of_coe_eq_scalar hc
            (hdet _ (R.mul_mem (R.mul_mem (R.mul_mem x.2 hb) (R.inv_mem x.2)) (R.inv_mem hb)))
      calc Nat.card θ.range ≤ Nat.card ((scalarSL3 K).prod (scalarSL3 K)) :=
            Subgroup.card_le_of_le hle
        _ = Nat.card (scalarSL3 K) * Nat.card (scalarSL3 K) := by
            rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
        _ ≤ 3 * 3 := Nat.mul_le_mul card_scalarSL3_le card_scalarSL3_le
        _ = 9 := by norm_num
    have hker : Nat.card θ.ker ≤ 3 := by
      have hle : θ.ker.map R.subtype ≤ scalarSL3 K := by
        rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
        have h1 := congrArg Prod.fst hx
        have h2 := congrArg Prod.snd hx
        simp only [θ, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_one, Prod.snd_one] at h1 h2
        have hxa : (x : GL (Fin 3) K) * a = a * x := by
          calc (x : GL (Fin 3) K) * a = x * a * (x : GL (Fin 3) K)⁻¹ * a⁻¹ * (a * x) := by group
            _ = a * x := by rw [h1, one_mul]
        have hxb : (x : GL (Fin 3) K) * b = b * x := by
          calc (x : GL (Fin 3) K) * b = x * b * (x : GL (Fin 3) K)⁻¹ * b⁻¹ * (b * x) := by group
            _ = b * x := by rw [h2, one_mul]
        obtain ⟨c, hc⟩ := scalar_of_commute_of_conj_eq_smul hω1 hωdet hP hev
          (A := ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
          (by rw [← Units.val_mul, hxa, Units.val_mul])
          (by rw [← Units.val_mul, hxb, Units.val_mul])
        exact mem_scalarSL3_of_coe_eq_scalar hc (hdet _ x.2)
      have h := (Subgroup.card_le_of_le hle).trans card_scalarSL3_le
      rwa [Subgroup.card_map_of_injective R.subtype_injective] at h
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv] at h1
    rw [h1]
    calc Nat.card θ.range * Nat.card θ.ker ≤ 9 * 3 := Nat.mul_le_mul hrange hker
      _ = 27 := by norm_num

end CFSG.RankThree.SubgroupLists

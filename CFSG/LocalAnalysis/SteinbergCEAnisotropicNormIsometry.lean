module

public import CFSG.LinearAlgebra.AnisotropicBinaryPlane
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Polynomial.SpecificDegree
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
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
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

namespace CFSG.LocalAnalysis

open Module Polynomial

variable {K : Type*} [Field K] [Fintype K] {E : Type*} [Field E] [Algebra K E]

theorem natCard_eq_sq_of_finrank_eq_two (hE : finrank K E = 2) :
    Nat.card E = Fintype.card K ^ 2 := by
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  rw [Module.natCard_eq_pow_finrank (K := K), hE, Nat.card_eq_fintype_card]

theorem pow_card_eq_self_iff (hE : finrank K E = 2) (z : E) :
    z ^ Fintype.card K = z ↔ z ∈ (algebraMap K E).range := by
  classical
  constructor
  · intro hz
    have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
    have : Finite E := Module.finite_of_finite K
    let := Fintype.ofFinite E
    have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
    set S := Finset.univ.filter fun w : E => w ^ Fintype.card K = w
    have hS : S.card ≤ Fintype.card K := by
      have hne := FiniteField.X_pow_card_sub_X_ne_zero E hq1
      calc S.card ≤ (X ^ Fintype.card K - X : E[X]).roots.toFinset.card := by
            refine Finset.card_le_card fun w hw => ?_
            rw [Multiset.mem_toFinset, mem_roots hne, IsRoot, eval_sub, eval_pow, eval_X,
              sub_eq_zero]
            exact (Finset.mem_filter.mp hw).2
        _ ≤ (X ^ Fintype.card K - X : E[X]).roots.card := Multiset.toFinset_card_le _
        _ ≤ (X ^ Fintype.card K - X : E[X]).natDegree := card_roots' _
        _ = Fintype.card K := FiniteField.X_pow_card_sub_X_natDegree_eq E hq1
    have himg : Finset.univ.image (algebraMap K E) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hw
        rw [Finset.mem_filter, ← map_pow, FiniteField.pow_card]
        exact ⟨Finset.mem_univ _, rfl⟩
      · rw [Finset.card_image_of_injective _ (algebraMap K E).injective, Finset.card_univ]
        exact hS
    have hzS : z ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    rw [← himg] at hzS
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hzS
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

theorem eq_pow_card_of_ne_one (hE : finrank K E = 2) {σ : E ≃ₐ[K] E} (hσ : σ ≠ 1) (z : E) :
    σ z = z ^ Fintype.card K := by
  classical
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional K E := this
  set φ := FiniteField.frobeniusAlgEquivOfAlgebraic K E
  have hφ : ∀ w, φ w = w ^ Fintype.card K := fun w => by
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
  have hq1 : 1 < Fintype.card K := Fintype.one_lt_card
  have hφ1 : φ ≠ 1 := by
    intro h
    have hall : ∀ w : E, w ∈ (algebraMap K E).range := fun w => by
      rw [← pow_card_eq_self_iff hE, ← hφ, h, AlgEquiv.one_apply]
    have hsurj : Function.Surjective (algebraMap K E) := fun w => hall w
    have h1 := Nat.card_le_card_of_surjective _ hsurj
    rw [natCard_eq_sq_of_finrank_eq_two hE, Nat.card_eq_fintype_card] at h1
    nlinarith
  by_contra hne
  have hσφ : σ ≠ φ := fun h => hne (by rw [h, hφ])
  have hcard := AlgEquiv.card_le (F := K) (K := E)
  rw [hE] at hcard
  have h3 : ({1, σ, φ} : Finset (E ≃ₐ[K] E)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hσφ]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hσ h.symm, fun h => hφ1 h.symm⟩
  have h4 := Finset.card_le_univ ({1, σ, φ} : Finset (E ≃ₐ[K] E))
  omega

theorem norm_range_and_kernel (hE : finrank K E = 2) {σ : E ≃ₐ[K] E} (hσ : σ ≠ 1) :
    (∀ z : E, z * σ z ∈ (algebraMap K E).range) ∧
    (∀ a : Kˣ, ∃ z : Eˣ, (z : E) * σ z = algebraMap K E a) ∧
    Nat.card {z : Eˣ // (z : E) * σ z = 1} = Fintype.card K + 1 := by
  classical
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  have : Finite E := Module.finite_of_finite K
  let := Fintype.ofFinite E
  set q := Fintype.card K with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have hEcard : Fintype.card E = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card, natCard_eq_sq_of_finrank_eq_two hE]
  have hN : ∀ z : E, z * σ z = z ^ (q + 1) := fun z => by
    rw [eq_pow_card_of_ne_one hE hσ, pow_succ', ← hq]
  have hval : ∀ z : E, z * σ z ∈ (algebraMap K E).range := by
    intro z
    rw [hN, ← pow_card_eq_self_iff hE, ← pow_mul]
    have h1 : (q + 1) * q = q ^ 2 + q := by ring
    rw [h1, pow_add, ← hEcard, FiniteField.pow_card, ← pow_succ']
  refine ⟨hval, ?_⟩
  set Nm : Eˣ →* Eˣ := powMonoidHom (q + 1)
  set KU : Subgroup Eˣ := (Units.map (algebraMap K E : K →* E)).range
  have hker : Nm.ker = rootsOfUnity (q + 1) E := by
    ext z
    rw [MonoidHom.mem_ker, mem_rootsOfUnity]
    rfl
  have hrange : Nm.range ≤ KU := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨a, ha⟩ := hval z
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact (mul_ne_zero z.ne_zero ((map_ne_zero σ).mpr z.ne_zero)) ha.symm
    refine ⟨Units.mk0 a ha0, Units.ext ?_⟩
    change algebraMap K E a = ((z ^ (q + 1) : Eˣ) : E)
    rw [ha, hN, Units.val_pow_eq_pow_val]
  have hKU : Nat.card KU = q - 1 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective (f := Units.map (algebraMap K E : K →* E))
      (Units.map_injective (algebraMap K E).injective)).toEquiv, Nat.card_eq_fintype_card,
      Fintype.card_units]
  have hEU : Nat.card Eˣ = q ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hEcard]
  have hlag : Nat.card Eˣ = Nat.card Nm.range * Nat.card Nm.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Nm.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange Nm).toEquiv]
  have hk : Nat.card Nm.ker ≤ q + 1 := by
    rw [hker]
    exact card_rootsOfUnity E (q + 1)
  have hr : Nat.card Nm.range ≤ q - 1 := hKU ▸ Subgroup.card_le_of_le hrange
  have hprod : (q - 1) * (q + 1) = q ^ 2 - 1 := by
    cases q with
    | zero => omega
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
  have hr' : Nat.card Nm.range = q - 1 := by
    by_contra hlt
    have hlt' : Nat.card Nm.range < q - 1 := lt_of_le_of_ne hr hlt
    have h1 : Nat.card Nm.range * Nat.card Nm.ker < (q - 1) * (q + 1) :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ hk) (Nat.mul_lt_mul_of_pos_right hlt' (by omega))
    omega
  have hk' : Nat.card Nm.ker = q + 1 := by
    rw [hEU, hr', ← hprod] at hlag
    exact (Nat.eq_of_mul_eq_mul_left (by omega) hlag).symm
  have hrangeKU : Nm.range = KU := Subgroup.eq_of_le_of_card_ge hrange (by rw [hKU, hr'])
  refine ⟨fun a => ?_, ?_⟩
  · have ha : Units.map (algebraMap K E : K →* E) a ∈ Nm.range := by
      rw [hrangeKU]
      exact ⟨a, rfl⟩
    obtain ⟨z, hz⟩ := ha
    refine ⟨z, ?_⟩
    rw [hN]
    have h1 := congrArg Units.val hz
    rw [Units.coe_map] at h1
    exact h1
  · rw [← hk', hker]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun z => by
      rw [mem_rootsOfUnity, hN, ← Units.val_pow_eq_pow_val, Units.val_eq_one]

variable [CharP K 2]

omit [Fintype K] in
theorem norm_anisotropic_nondegenerate {σ : E ≃ₐ[K] E} (hσ : σ ≠ 1) :
    (∀ z : E, z * σ z = 0 → z = 0) ∧
    ∀ z : E, (∀ w : E, (z + w) * σ (z + w) - z * σ z - w * σ w = 0) → z = 0 := by
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  have hani : ∀ z : E, z * σ z = 0 → z = 0 := fun z hz => by
    rcases mul_eq_zero.mp hz with h | h
    · exact h
    · exact (map_eq_zero_iff σ σ.injective).mp h
  refine ⟨hani, fun z hz => ?_⟩
  by_contra hz0
  obtain ⟨ζ, hζ⟩ : ∃ ζ : E, σ ζ ≠ ζ := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  have h1 := hz (z * ζ)
  have h2 : (z + z * ζ) * σ (z + z * ζ) - z * σ z - z * ζ * σ (z * ζ) =
      z * σ z * (σ ζ + ζ) := by
    rw [map_add, map_mul]
    ring
  rw [h2] at h1
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact hz0 (hani z h3)
  · apply hζ
    have h4 := eq_neg_of_add_eq_zero_left h3
    rwa [CharTwo.neg_eq] at h4

theorem exists_root_quadratic (hE : finrank K E = 2) {ε : K}
    (hQ : ∀ x y : K, x ^ 2 + ε * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0) :
    ∃ ζ : E, ζ ^ 2 + algebraMap K E ε * ζ + 1 = 0 := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : Fact (∀ r : K, r ^ 2 ≠ 1 + ε * r) :=
    ⟨CFSG.LinearAlgebra.sq_ne_one_add_mul_of_anisotropic hQ⟩
  let : Fintype (QuadraticAlgebra K 1 ε) :=
    Fintype.ofEquiv (K × K) (QuadraticAlgebra.equivProd 1 ε).symm
  have hLcard : Fintype.card (QuadraticAlgebra K 1 ε) = Fintype.card K ^ 2 := by
    rw [Fintype.card_congr (QuadraticAlgebra.equivProd 1 ε), Fintype.card_prod, sq]
  set ω : QuadraticAlgebra K 1 ε := ⟨0, 1⟩
  set f : K[X] := X ^ 2 + C ε * X + 1 with hf
  have hf_monic : f.Monic := by
    rw [hf]
    monicity!
  have hf_deg : f.natDegree = 2 := by
    rw [hf]
    compute_degree!
  have hf_irr : Irreducible f := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hf_deg]; decide) fun r h => ?_
    have h1 := hQ r 1 (by
      have h3 : f.eval r = 0 := h
      simpa [hf] using h3)
    exact one_ne_zero h1.2
  have hω : aeval ω f = 0 := by
    simp only [hf, map_add, map_mul, map_pow, aeval_X, aeval_C, map_one]
    ext
    · simp [ω, pow_two, QuadraticAlgebra.re_one]
      linear_combination h2
    · simp [ω, pow_two, QuadraticAlgebra.im_one]
      linear_combination ε * h2
  have hdvd : f ∣ X ^ (Fintype.card K ^ 2) - X := by
    rw [minpoly.eq_of_irreducible_of_monic hf_irr hω hf_monic]
    apply minpoly.dvd
    rw [map_sub, map_pow, aeval_X, ← hLcard, FiniteField.pow_card, sub_self]
  have : Module.Finite K E := Module.finite_of_finrank_eq_succ hE
  have : Finite E := Module.finite_of_finite K
  let := Fintype.ofFinite E
  have hEcard : Fintype.card E = Fintype.card K ^ 2 := by
    rw [← Nat.card_eq_fintype_card, natCard_eq_sq_of_finrank_eq_two hE]
  have hsplit := IsSplittingField.splits E (X ^ Fintype.card E - X : K[X])
  rw [hEcard] at hsplit
  have hq1 : 1 < Fintype.card K ^ 2 := by
    have := Fintype.one_lt_card (α := K)
    nlinarith
  have hne : (X ^ (Fintype.card K ^ 2) - X : K[X]).map (algebraMap K E) ≠ 0 := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X]
    exact FiniteField.X_pow_card_sub_X_ne_zero E hq1
  have hfsplit := hsplit.of_dvd hne (Polynomial.map_dvd _ hdvd)
  obtain ⟨ζ, hζ⟩ := hfsplit.exists_eval_eq_zero (by
    rw [degree_map, Polynomial.degree_eq_natDegree hf_monic.ne_zero, hf_deg]
    decide)
  refine ⟨ζ, ?_⟩
  simpa [hf] using hζ

theorem anisotropic_plane_isometry (hE : finrank K E = 2) {σ : E ≃ₐ[K] E} (hσ : σ ≠ 1)
    {A : Type*} [AddCommGroup A] [Module K A] (hA : finrank K A = 2) (R : QuadraticForm K A)
    (hRan : ∀ x, R x = 0 → x = 0) (hRnd : (QuadraticMap.polarBilin R).Nondegenerate) :
    (∃ u v : A, LinearIndependent K ![u, v] ∧ R u = 1 ∧ R v = 1) ∧
    ∀ u v : A, LinearIndependent K ![u, v] → R u = 1 → R v = 1 →
      QuadraticMap.polar R u v ≠ 0 ∧
      (∃ ζ : E, ζ ^ 2 + algebraMap K E (QuadraticMap.polar R u v) * ζ + 1 = 0) ∧
      ∀ ζ : E, ζ ^ 2 + algebraMap K E (QuadraticMap.polar R u v) * ζ + 1 = 0 →
        ζ ∉ (algebraMap K E).range ∧ ∃ θ : A ≃ₗ[K] E,
          (∀ s t : K, θ (s • u + t • v) = algebraMap K E s + algebraMap K E t * ζ) ∧
          ∀ x, θ x * σ (θ x) = algebraMap K E (R x) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  have h2E : (2 : E) = 0 := CharTwo.two_eq_zero
  have hRlin : ∀ (u v : A) (x y : K), R (x • u + y • v) =
      x ^ 2 * R u + y ^ 2 * R v + x * y * QuadraticMap.polar R u v := by
    intro u v x y
    have h1 : R (x • u + y • v) = R (x • u) + R (y • v) + QuadraticMap.polar R (x • u) (y • v) := by
      rw [QuadraticMap.polar]
      ring
    rw [h1, QuadraticMap.map_smul, QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨?_, fun u v hli hu hv => ?_⟩
  ·
    have : Module.Finite K A := Module.finite_of_finrank_eq_succ hA
    let b := Module.finBasisOfFinrankEq K A hA
    have hsq : ∀ i, ∃ c : K, c ≠ 0 ∧ R (b i) = c * c := by
      intro i
      obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (R (b i))
      refine ⟨c, fun h => b.ne_zero i (hRan _ (by rw [hc, h, mul_zero])), hc⟩
    choose c hc0 hc using hsq
    let w : Fin 2 → Kˣ := fun i => (Units.mk0 (c i) (hc0 i))⁻¹
    refine ⟨(c 0)⁻¹ • b 0, (c 1)⁻¹ • b 1, ?_, ?_, ?_⟩
    · have h := b.linearIndependent.units_smul w
      convert h using 1
      funext i
      fin_cases i <;> rfl
    · rw [QuadraticMap.map_smul, hc, smul_eq_mul,
        show (c 0)⁻¹ * (c 0)⁻¹ * (c 0 * c 0) = ((c 0)⁻¹ * c 0) * ((c 0)⁻¹ * c 0) by ring,
        inv_mul_cancel₀ (hc0 0), one_mul]
    · rw [QuadraticMap.map_smul, hc, smul_eq_mul,
        show (c 1)⁻¹ * (c 1)⁻¹ * (c 1 * c 1) = ((c 1)⁻¹ * c 1) * ((c 1)⁻¹ * c 1) by ring,
        inv_mul_cancel₀ (hc0 1), one_mul]
  set ε := QuadraticMap.polar R u v with hε
  set bA := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hA])
  have hbA : ∀ i, bA i = ![u, v] i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  have hdecomp : ∀ x, x = bA.repr x 0 • u + bA.repr x 1 • v := by
    intro x
    conv_lhs => rw [← bA.sum_repr x]
    rw [Fin.sum_univ_two, hbA, hbA]
    rfl
  have hε0 : ε ≠ 0 := by
    intro h0
    apply hli.ne_zero 0
    simp only [Matrix.cons_val_zero]
    apply hRnd.1 u
    intro x
    rw [hdecomp x]
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_self, ← hε, h0, hu, smul_eq_mul,
      nsmul_eq_mul, Nat.cast_ofNat, h2, zero_mul, mul_zero, add_zero]
  have hQ : ∀ x y : K, x ^ 2 + ε * x * y + y ^ 2 = 0 → x = 0 ∧ y = 0 := by
    intro x y hxy
    have h1 : R (x • u + y • v) = 0 := by
      rw [hRlin, hu, hv, ← hε]
      linear_combination hxy
    exact LinearIndependent.pair_iff.mp hli x y (hRan _ h1)
  refine ⟨hε0, exists_root_quadratic hE hQ, fun ζ hζ => ?_⟩
  have hζK : ζ ∉ (algebraMap K E).range := by
    rintro ⟨r, rfl⟩
    have h1 : algebraMap K E (r ^ 2 + ε * r * 1 + 1 ^ 2) = 0 := by
      rw [← hζ]
      simp only [map_add, map_mul, map_pow, map_one]
      ring
    exact one_ne_zero (hQ r 1 ((map_eq_zero_iff _ (algebraMap K E).injective).mp h1)).2
  have hσζ : σ ζ = ζ + algebraMap K E ε := by
    have hroot : σ ζ ^ 2 + algebraMap K E ε * σ ζ + 1 = 0 := by
      have h1 := congrArg σ hζ
      rwa [map_add, map_add, map_mul, map_pow, AlgEquiv.commutes, map_one, map_zero] at h1
    have hne : σ ζ ≠ ζ := by
      intro h1
      apply hζK
      rw [← pow_card_eq_self_iff hE, ← eq_pow_card_of_ne_one hE hσ]
      exact h1
    have hprod : (σ ζ - ζ) * (σ ζ - (ζ + algebraMap K E ε)) = 0 := by
      linear_combination hroot + hζ - (σ ζ * ζ + σ ζ * algebraMap K E ε + 1) * h2E
    rcases mul_eq_zero.mp hprod with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne
    · exact sub_eq_zero.mp h1
  have hliE : LinearIndependent K ![(1 : E), ζ] := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul, add_zero, smul_eq_zero] at hac
      exact ⟨hac.resolve_right one_ne_zero, rfl⟩
    · exfalso
      apply hζK
      refine ⟨-(a / c), ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hac
      have hc' : algebraMap K E c ≠ 0 := (_root_.map_ne_zero (algebraMap K E)).mpr hc
      have hζeq : ζ = -(algebraMap K E a) / algebraMap K E c := by
        rw [eq_div_iff hc']
        linear_combination hac
      rw [hζeq, map_neg, map_div₀, neg_div]
  set bE := basisOfLinearIndependentOfCardEqFinrank hliE (by rw [Fintype.card_fin, hE])
  have hbE : ∀ i, bE i = ![(1 : E), ζ] i := fun i => by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  set θ := bA.equiv bE (Equiv.refl _)
  have hθ : ∀ s t : K, θ (s • u + t • v) = algebraMap K E s + algebraMap K E t * ζ := by
    intro s t
    have hu' : θ u = 1 := by
      have h1 := Module.Basis.equiv_apply bA 0 bE (Equiv.refl _)
      rw [hbA, hbE] at h1
      simpa using h1
    have hv' : θ v = ζ := by
      have h1 := Module.Basis.equiv_apply bA 1 bE (Equiv.refl _)
      rw [hbA, hbE] at h1
      simpa using h1
    rw [map_add, map_smul, map_smul, hu', hv', Algebra.smul_def, Algebra.smul_def, mul_one]
  refine ⟨hζK, θ, hθ, fun x => ?_⟩
  rw [hdecomp x, hθ, hRlin, hu, hv, ← hε, map_add, map_mul, AlgEquiv.commutes,
    AlgEquiv.commutes, hσζ]
  simp only [map_add, map_mul, map_pow, mul_one]
  linear_combination (algebraMap K E (bA.repr x 1)) ^ 2 * hζ +
    (algebraMap K E (bA.repr x 0) * algebraMap K E (bA.repr x 1) * ζ -
      (algebraMap K E (bA.repr x 1)) ^ 2) * h2E

theorem even_anisotropic_plane_fixed_norm_isometry (hE : finrank K E = 2) {σ : E ≃ₐ[K] E}
    (hσ : σ ≠ 1) :
    Nat.card E = Fintype.card K ^ 2 ∧ (∀ z, σ z = z ^ Fintype.card K) ∧
    (∀ z : E, z * σ z ∈ (algebraMap K E).range) ∧
    (∀ a : Kˣ, ∃ z : Eˣ, (z : E) * σ z = algebraMap K E a) ∧
    Nat.card {z : Eˣ // (z : E) * σ z = 1} = Fintype.card K + 1 ∧
    (∀ z : E, z * σ z = 0 → z = 0) ∧
    (∀ z : E, (∀ w : E, (z + w) * σ (z + w) - z * σ z - w * σ w = 0) → z = 0) ∧
    ∀ {A : Type*} [AddCommGroup A] [Module K A], finrank K A = 2 → ∀ R : QuadraticForm K A,
      (∀ x, R x = 0 → x = 0) → (QuadraticMap.polarBilin R).Nondegenerate →
      (∃ θ : A ≃ₗ[K] E, ∀ x, θ x * σ (θ x) = algebraMap K E (R x)) ∧
      (∃ u v : A, LinearIndependent K ![u, v] ∧ R u = 1 ∧ R v = 1) ∧
      ∀ u v : A, LinearIndependent K ![u, v] → R u = 1 → R v = 1 →
        QuadraticMap.polar R u v ≠ 0 ∧
        (∃ ζ : E, ζ ^ 2 + algebraMap K E (QuadraticMap.polar R u v) * ζ + 1 = 0) ∧
        ∀ ζ : E, ζ ^ 2 + algebraMap K E (QuadraticMap.polar R u v) * ζ + 1 = 0 →
          ζ ∉ (algebraMap K E).range ∧ ∃ θ : A ≃ₗ[K] E,
            (∀ s t : K, θ (s • u + t • v) = algebraMap K E s + algebraMap K E t * ζ) ∧
            ∀ x, θ x * σ (θ x) = algebraMap K E (R x) := by
  obtain ⟨hval, hsurj, hker⟩ := norm_range_and_kernel hE hσ
  obtain ⟨hani, hnd⟩ := norm_anisotropic_nondegenerate (K := K) hσ
  refine ⟨natCard_eq_sq_of_finrank_eq_two hE, eq_pow_card_of_ne_one hE hσ, hval, hsurj, hker,
    hani, hnd, fun {A} _ _ hA R hRan hRnd => ?_⟩
  obtain ⟨hex, hall⟩ := anisotropic_plane_isometry hE hσ hA R hRan hRnd
  refine ⟨?_, hex, hall⟩
  obtain ⟨u, v, hli, hu, hv⟩ := hex
  obtain ⟨-, ⟨ζ, hζ⟩, hroot⟩ := hall u v hli hu hv
  obtain ⟨-, θ, -, hθ⟩ := hroot ζ hζ
  exact ⟨θ, hθ⟩

end CFSG.LocalAnalysis

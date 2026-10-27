module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne.KCPrimary

open Polynomial Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

open scoped _root_.Classical in
@[expose] noncomputable def primaryFactors (x : Module.End K V) : Finset K[X] :=
  (UniqueFactorizationMonoid.normalizedFactors (minpoly K x)).toFinset

section Factors

variable [FiniteDimensional K V] {x : Module.End K V}

theorem minpoly_ne_zero (x : Module.End K V) : minpoly K x ≠ 0 :=
  minpoly.ne_zero (Algebra.IsIntegral.isIntegral x)

theorem mem_primaryFactors {a : K[X]} :
    a ∈ primaryFactors x ↔ Irreducible a ∧ a.Monic ∧ a ∣ minpoly K x := by
  classical
  unfold primaryFactors
  rw [Multiset.mem_toFinset]
  exact Polynomial.mem_normalizedFactors_iff (minpoly_ne_zero x)

theorem irreducible_of_mem_primaryFactors {a : K[X]} (ha : a ∈ primaryFactors x) :
    Irreducible a := (mem_primaryFactors.mp ha).1

theorem monic_of_mem_primaryFactors {a : K[X]} (ha : a ∈ primaryFactors x) : a.Monic :=
  (mem_primaryFactors.mp ha).2.1

theorem isCoprime_of_mem_primaryFactors {a b : K[X]} (ha : a ∈ primaryFactors x)
    (hb : b ∈ primaryFactors x) (hab : a ≠ b) : IsCoprime a b := by
  have hai := irreducible_of_mem_primaryFactors ha
  rw [hai.coprime_iff_not_dvd]
  intro hdvd
  have hbi := irreducible_of_mem_primaryFactors hb
  have hass : Associated a b := hai.associated_of_dvd hbi hdvd
  exact hab (eq_of_monic_of_associated (monic_of_mem_primaryFactors ha)
    (monic_of_mem_primaryFactors hb) hass)

theorem pairwise_isCoprime_primaryFactors :
    (primaryFactors x : Set K[X]).Pairwise IsCoprime := fun _ ha _ hb hab =>
  isCoprime_of_mem_primaryFactors ha hb hab

theorem prod_primaryFactors (hx : Squarefree (minpoly K x)) :
    ∏ a ∈ primaryFactors x, a = minpoly K x := by
  classical
  have hnd := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    (minpoly_ne_zero x)).mp hx
  have h1 : ∏ a ∈ primaryFactors x, a = (UniqueFactorizationMonoid.normalizedFactors
      (minpoly K x)).prod := by
    unfold primaryFactors
    rw [Finset.prod_eq_multiset_prod, ← Multiset.toFinset_eq hnd]
    simp
  rw [h1]
  have := Polynomial.leadingCoeff_mul_prod_normalizedFactors (minpoly K x)
  rwa [(minpoly.monic (Algebra.IsIntegral.isIntegral x)).leadingCoeff, C_1, one_mul] at this

end Factors

@[expose] noncomputable def primaryComponent (x : Module.End K V) (a : K[X]) : Submodule K V :=
  LinearMap.ker (aeval x a)

theorem mem_primaryComponent {x : Module.End K V} {a : K[X]} {v : V} :
    v ∈ primaryComponent x a ↔ aeval x a v = 0 := LinearMap.mem_ker

theorem commute_aeval {r x : Module.End K V} (h : Commute r x) (f : K[X]) :
    Commute r (aeval x f) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial n c =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right c r).mul_right (h.pow_right n)

theorem apply_mem_primaryComponent {r x : Module.End K V} (h : Commute r x) {a : K[X]} {v : V}
    (hv : v ∈ primaryComponent x a) : r v ∈ primaryComponent x a := by
  rw [mem_primaryComponent] at hv ⊢
  have := (commute_aeval h a).eq
  calc aeval x a (r v) = (aeval x a * r) v := rfl
    _ = (r * aeval x a) v := by rw [this]
    _ = 0 := by simp [Module.End.mul_apply, hv]

section Idempotents

variable [FiniteDimensional K V] {x : Module.End K V}

open scoped _root_.Classical in
theorem isCoprime_prod_erase {a : K[X]} (ha : a ∈ primaryFactors x) :
    IsCoprime a (∏ b ∈ (primaryFactors x).erase a, b) :=
  IsCoprime.prod_right fun _ hb => isCoprime_of_mem_primaryFactors ha
    (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm

open scoped _root_.Classical in
theorem exists_primaryIdempotent (hx : Squarefree (minpoly K x)) {a : K[X]}
    (ha : a ∈ primaryFactors x) :
    ∃ ε : K[X], a ∣ ε - 1 ∧ (∀ b ∈ primaryFactors x, b ≠ a → b ∣ ε) ∧
      minpoly K x ∣ a * ε := by
  obtain ⟨u, v, huv⟩ := isCoprime_prod_erase ha
  refine ⟨v * ∏ b ∈ (primaryFactors x).erase a, b, ⟨-u, ?_⟩, fun b hb hba => ?_, ?_⟩
  · linear_combination huv
  · exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hba, hb⟩)) v
  · refine ⟨v, ?_⟩
    rw [← prod_primaryFactors hx, ← Finset.mul_prod_erase _ _ ha]
    ring

open scoped _root_.Classical in
noncomputable def primaryIdempotent (x : Module.End K V) (a : K[X]) : K[X] :=
  if h : ∃ ε : K[X], a ∣ ε - 1 ∧ (∀ b ∈ primaryFactors x, b ≠ a → b ∣ ε) ∧
      minpoly K x ∣ a * ε then h.choose else 0

theorem primaryIdempotent_spec (hx : Squarefree (minpoly K x)) {a : K[X]}
    (ha : a ∈ primaryFactors x) :
    a ∣ primaryIdempotent x a - 1 ∧ (∀ b ∈ primaryFactors x, b ≠ a → b ∣ primaryIdempotent x a) ∧
      minpoly K x ∣ a * primaryIdempotent x a := by
  have h := exists_primaryIdempotent hx ha
  simp only [primaryIdempotent, h, ↓reduceDIte]
  exact h.choose_spec

@[expose] noncomputable def primaryProjection (x : Module.End K V) (a : K[X]) : Module.End K V :=
  aeval x (primaryIdempotent x a)

theorem primaryProjection_mem (hx : Squarefree (minpoly K x)) {a : K[X]}
    (ha : a ∈ primaryFactors x) (v : V) : primaryProjection x a v ∈ primaryComponent x a := by
  obtain ⟨-, -, ⟨q, hq⟩⟩ := primaryIdempotent_spec hx ha
  rw [mem_primaryComponent, primaryProjection, ← Module.End.mul_apply, ← map_mul, hq, map_mul,
    minpoly.aeval, zero_mul]
  rfl

theorem primaryProjection_of_mem (hx : Squarefree (minpoly K x)) {a : K[X]}
    (ha : a ∈ primaryFactors x) {v : V} (hv : v ∈ primaryComponent x a) :
    primaryProjection x a v = v := by
  obtain ⟨⟨q, hq⟩, -, -⟩ := primaryIdempotent_spec hx ha
  have hε : primaryIdempotent x a = 1 + q * a := by linear_combination hq
  rw [primaryProjection, hε, map_add, map_one, map_mul]
  simp [Module.End.mul_apply, mem_primaryComponent.mp hv]


open scoped _root_.Classical in
theorem primaryProjection_of_mem_ne (hx : Squarefree (minpoly K x)) {a b : K[X]}
    (ha : a ∈ primaryFactors x) (hb : b ∈ primaryFactors x) (hab : b ≠ a) {v : V}
    (hv : v ∈ primaryComponent x b) : primaryProjection x a v = 0 := by
  obtain ⟨-, hdiv, -⟩ := primaryIdempotent_spec hx ha
  obtain ⟨q, hq⟩ := hdiv b hb hab
  rw [primaryProjection, hq, mul_comm, map_mul]
  simp [Module.End.mul_apply, mem_primaryComponent.mp hv]

open scoped _root_.Classical in
theorem sum_primaryProjection (hx : Squarefree (minpoly K x)) :
    ∑ a ∈ primaryFactors x, primaryProjection x a = 1 := by
  have hdvd : minpoly K x ∣ (∑ a ∈ primaryFactors x, primaryIdempotent x a) - 1 := by
    rw [← prod_primaryFactors hx]
    refine Finset.prod_dvd_of_coprime pairwise_isCoprime_primaryFactors fun b hb => ?_
    rw [← Finset.add_sum_erase _ _ hb, add_sub_right_comm]
    refine dvd_add (primaryIdempotent_spec hx hb).1 (Finset.dvd_sum fun c hc => ?_)
    exact (primaryIdempotent_spec hx (Finset.mem_of_mem_erase hc)).2.1 b hb
      (Finset.ne_of_mem_erase hc).symm
  obtain ⟨q, hq⟩ := hdvd
  have h1 : (∑ a ∈ primaryFactors x, primaryProjection x a) - 1 = aeval x (minpoly K x * q) := by
    rw [← hq]; simp [primaryProjection]
  rw [map_mul, minpoly.aeval, zero_mul, sub_eq_zero] at h1
  exact h1


variable (x) in
noncomputable def primaryCoords (hx : Squarefree (minpoly K x)) :
    V →ₗ[K] ((a : primaryFactors x) → primaryComponent x a) :=
  LinearMap.pi fun a => (primaryProjection x a).codRestrict (primaryComponent x a)
    (primaryProjection_mem hx a.2)

variable (x) in
noncomputable def primarySum : ((a : primaryFactors x) → primaryComponent x a) →ₗ[K] V :=
  ∑ a : primaryFactors x, (primaryComponent x a).subtype ∘ₗ LinearMap.proj a

theorem primarySum_primaryCoords (hx : Squarefree (minpoly K x)) (v : V) :
    primarySum x (primaryCoords x hx v) = v := by
  classical
  have h := LinearMap.congr_fun (sum_primaryProjection hx) v
  rw [LinearMap.sum_apply] at h
  simp only [primarySum, primaryCoords, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.pi_apply, LinearMap.codRestrict_apply,
    Submodule.subtype_apply]
  rw [Finset.sum_coe_sort (primaryFactors x) (fun a => primaryProjection x a v)]
  simpa using h

@[simp] theorem coe_primaryCoords (hx : Squarefree (minpoly K x)) (v : V)
    (b : primaryFactors x) : (primaryCoords x hx v b : V) = primaryProjection x b v := by
  simp [primaryCoords]

omit [FiniteDimensional K V] in
theorem primarySum_apply (w : (a : primaryFactors x) → primaryComponent x a) :
    primarySum x w = ∑ a : primaryFactors x, (w a : V) := by
  simp [primarySum]

theorem primaryCoords_primarySum (hx : Squarefree (minpoly K x))
    (w : (a : primaryFactors x) → primaryComponent x a) :
    primaryCoords x hx (primarySum x w) = w := by
  classical
  funext b
  apply Subtype.ext
  rw [coe_primaryCoords, primarySum_apply, map_sum]
  rw [Finset.sum_eq_single b]
  · exact primaryProjection_of_mem hx b.2 (w b).2
  · intro a _ hab
    exact primaryProjection_of_mem_ne hx b.2 a.2 (fun h => hab (Subtype.ext h)) (w a).2
  · intro h
    exact absurd (Finset.mem_univ b) h

@[expose] noncomputable def primaryEquivPi (hx : Squarefree (minpoly K x)) :
    V ≃ₗ[K] ((a : primaryFactors x) → primaryComponent x a) :=
  LinearEquiv.ofLinearMap (primaryCoords x hx) (primarySum x)
    (LinearMap.ext (primaryCoords_primarySum hx)) (LinearMap.ext (primarySum_primaryCoords hx))

end Idempotents

section ModuleStructure

variable (x : Module.End K V) (a : K[X])

@[expose] noncomputable def primaryRestrict : Module.End K (primaryComponent x a) :=
  x.restrict fun _ hv => apply_mem_primaryComponent (Commute.refl x) hv

@[simp] theorem coe_primaryRestrict (v : primaryComponent x a) :
    ((primaryRestrict x a v : primaryComponent x a) : V) = x v := rfl

theorem coe_pow_primaryRestrict (n : ℕ) (v : primaryComponent x a) :
    ((((primaryRestrict x a) ^ n) v : primaryComponent x a) : V) = (x ^ n) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

theorem coe_aeval_primaryRestrict (f : K[X]) (v : primaryComponent x a) :
    ((aeval (primaryRestrict x a) f v : primaryComponent x a) : V) = aeval x f (v : V) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp [aeval_monomial, coe_pow_primaryRestrict]

theorem aeval_primaryRestrict_self : aeval (primaryRestrict x a) a = 0 := by
  ext v
  rw [coe_aeval_primaryRestrict]
  exact mem_primaryComponent.mp v.2

@[expose] noncomputable def primaryAction :
    AdjoinRoot a →ₐ[K] Module.End K (primaryComponent x a) :=
  Ideal.Quotient.liftₐ (Ideal.span {a}) (aeval (primaryRestrict x a)) fun f hf => by
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    rw [map_mul, aeval_primaryRestrict_self, zero_mul]


noncomputable instance primaryComponent.instModule :
    Module (AdjoinRoot a) (primaryComponent x a) :=
  Module.compHom _ (primaryAction x a).toRingHom

theorem primaryComponent.smul_eq (e : AdjoinRoot a) (v : primaryComponent x a) :
    e • v = primaryAction x a e v := rfl

@[simp] theorem coe_mk_smul_primaryComponent (f : K[X]) (v : primaryComponent x a) :
    ((AdjoinRoot.mk a f • v : primaryComponent x a) : V) = aeval x f (v : V) := by
  rw [primaryComponent.smul_eq]
  change ((aeval (primaryRestrict x a) f v : primaryComponent x a) : V) = _
  exact coe_aeval_primaryRestrict x a f v

@[simp] theorem coe_root_smul_primaryComponent (v : primaryComponent x a) :
    ((AdjoinRoot.root a • v : primaryComponent x a) : V) = x (v : V) := by
  rw [AdjoinRoot.root, coe_mk_smul_primaryComponent]
  simp

instance : IsScalarTower K (AdjoinRoot a) (primaryComponent x a) where
  smul_assoc c e v := by
    change primaryAction x a (c • e) v = c • primaryAction x a e v
    rw [map_smul]
    rfl

instance : SMulCommClass (AdjoinRoot a) K (primaryComponent x a) where
  smul_comm e c v := by
    change primaryAction x a e (c • v) = c • primaryAction x a e v
    rw [map_smul]

theorem coe_algebraMap_smul_primaryComponent (c : K) (v : primaryComponent x a) :
    ((algebraMap K (AdjoinRoot a) c • v : primaryComponent x a) : V) = c • (v : V) := by
  rw [algebraMap_smul]
  rfl

instance [FiniteDimensional K V] : Module.Finite (AdjoinRoot a) (primaryComponent x a) :=
  Module.Finite.of_restrictScalars_finite K (AdjoinRoot a) (primaryComponent x a)

theorem finrank_primaryComponent [FiniteDimensional K V] [Fact (Irreducible a)] :
    Module.finrank K (primaryComponent x a) =
      a.natDegree * Module.finrank (AdjoinRoot a) (primaryComponent x a) := by
  rw [← Module.finrank_mul_finrank K (AdjoinRoot a) (primaryComponent x a),
    (AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finrank, AdjoinRoot.powerBasis_dim]

end ModuleStructure

section Commutant

variable (x : Module.End K V)

abbrev commutant : Subalgebra K (Module.End K V) := Subalgebra.centralizer K {x}

theorem mem_commutant {r : Module.End K V} : r ∈ commutant x ↔ Commute r x := by
  rw [Subalgebra.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [commute_iff_eq, eq_comm]


variable {x}

@[expose] noncomputable def commutantRestrict (a : K[X]) (r : commutant x) :
    Module.End (AdjoinRoot a) (primaryComponent x a) where
  toFun v := ⟨r.1 (v : V), apply_mem_primaryComponent ((mem_commutant x).mp r.2) v.2⟩
  map_add' u v := Subtype.ext (map_add r.1 (u : V) (v : V))
  map_smul' e v := by
    induction e using AdjoinRoot.induction_on with
    | _ f =>
      apply Subtype.ext
      simp only [coe_mk_smul_primaryComponent, RingHom.id_apply]
      exact congrArg (fun T : Module.End K V => T (v : V))
        (commute_aeval ((mem_commutant x).mp r.2) f).eq

@[simp] theorem coe_commutantRestrict (a : K[X]) (r : commutant x) (v : primaryComponent x a) :
    ((commutantRestrict a r v : primaryComponent x a) : V) = r.1 v := rfl

@[expose] noncomputable def commutantRestrictHom (a : K[X]) :
    commutant x →ₐ[K] Module.End (AdjoinRoot a) (primaryComponent x a) where
  toFun := commutantRestrict a
  map_one' := by ext v; rfl
  map_mul' r s := by ext v; rfl
  map_zero' := by ext v; rfl
  map_add' r s := by ext v; rfl
  commutes' c := by
    ext v
    rw [coe_commutantRestrict]
    have h1 : ((algebraMap K (commutant x) c).1 : Module.End K V) =
        algebraMap K (Module.End K V) c := rfl
    rw [h1, Module.algebraMap_end_apply, Module.algebraMap_end_apply]
    rfl

@[simp] theorem coe_commutantRestrictHom (a : K[X]) (r : commutant x)
    (v : primaryComponent x a) :
    ((commutantRestrictHom a r v : primaryComponent x a) : V) = r.1 v := rfl


theorem ext_primaryComponent [FiniteDimensional K V] (hx : Squarefree (minpoly K x))
    {M : Type*} [AddCommGroup M] [Module K M] {f g : V →ₗ[K] M}
    (h : ∀ a ∈ primaryFactors x, ∀ v ∈ primaryComponent x a, f v = g v) : f = g := by
  classical
  ext v
  have hv : v = ∑ a ∈ primaryFactors x, primaryProjection x a v := by
    have := LinearMap.congr_fun (sum_primaryProjection hx) v
    rw [LinearMap.sum_apply] at this
    simpa using this.symm
  rw [hv, map_sum, map_sum]
  exact Finset.sum_congr rfl fun a ha => h a ha _ (primaryProjection_mem hx ha v)

@[expose] noncomputable def primaryGlue [FiniteDimensional K V] (hx : Squarefree (minpoly K x))
    (γ : (a : primaryFactors x) →
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X]))) : Module.End K V :=
  primarySum x ∘ₗ (LinearMap.pi fun a => ((γ a).restrictScalars K) ∘ₗ LinearMap.proj a) ∘ₗ
    primaryCoords x hx

theorem primaryGlue_apply_of_mem [FiniteDimensional K V] (hx : Squarefree (minpoly K x))
    (γ : (a : primaryFactors x) →
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X])))
    {b : primaryFactors x} {v : V} (hv : v ∈ primaryComponent x (b : K[X])) :
    (primaryGlue hx γ v : V) = ((γ b ⟨v, hv⟩ : primaryComponent x (b : K[X])) : V) := by
  classical
  have hcoord : primaryCoords x hx v = Pi.single b ⟨v, hv⟩ := by
    funext a
    apply Subtype.ext
    rw [coe_primaryCoords]
    by_cases hab : a = b
    · subst hab
      simp [primaryProjection_of_mem hx a.2 hv]
    · rw [Pi.single_eq_of_ne hab]
      exact primaryProjection_of_mem_ne hx a.2 b.2 (fun h => hab (Subtype.ext h.symm)) hv
  rw [primaryGlue, LinearMap.comp_apply, LinearMap.comp_apply, hcoord, primarySum_apply]
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    LinearMap.coe_restrictScalars]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ hab
    rw [Pi.single_eq_of_ne hab, map_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ b) h


theorem primaryGlue_mem_commutant [FiniteDimensional K V] (hx : Squarefree (minpoly K x))
    (γ : (a : primaryFactors x) →
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X]))) :
    primaryGlue hx γ ∈ commutant x := by
  rw [mem_commutant, commute_iff_eq]
  refine ext_primaryComponent hx (fun b hb v hv => ?_)
  have hxv : x v ∈ primaryComponent x b := apply_mem_primaryComponent (Commute.refl x) hv
  change primaryGlue hx γ (x v) = x (primaryGlue hx γ v)
  rw [primaryGlue_apply_of_mem hx γ (b := ⟨b, hb⟩) hxv,
    primaryGlue_apply_of_mem hx γ (b := ⟨b, hb⟩) hv]
  have h1 : (⟨x v, hxv⟩ : primaryComponent x b) =
      AdjoinRoot.root b • (⟨v, hv⟩ : primaryComponent x b) :=
    Subtype.ext (by rw [coe_root_smul_primaryComponent])
  rw [h1, map_smul, coe_root_smul_primaryComponent]

@[expose] noncomputable def commutantToPi :
    commutant x →ₐ[K] ((a : primaryFactors x) →
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X]))) :=
  AlgHom.pi fun a => commutantRestrictHom (a : K[X])

theorem commutantToPi_bijective [FiniteDimensional K V] (hx : Squarefree (minpoly K x)) :
    Function.Bijective (commutantToPi (x := x)) := by
  constructor
  · intro r s hrs
    apply Subtype.ext
    refine ext_primaryComponent hx (fun a ha v hv => ?_)
    have h1 := congrArg (fun T => ((T ⟨v, hv⟩ : primaryComponent x a) : V))
      (congrFun hrs ⟨a, ha⟩)
    exact h1
  · intro γ
    refine ⟨⟨primaryGlue hx γ, primaryGlue_mem_commutant hx γ⟩, ?_⟩
    funext a
    ext v
    exact primaryGlue_apply_of_mem hx γ v.2

@[expose] noncomputable def commutantEquivPi [FiniteDimensional K V]
    (hx : Squarefree (minpoly K x)) :
    commutant x ≃ₐ[K] ((a : primaryFactors x) →
      Module.End (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X]))) :=
  AlgEquiv.ofBijective commutantToPi (commutantToPi_bijective hx)

@[simp] theorem coe_commutantEquivPi_apply [FiniteDimensional K V]
    (hx : Squarefree (minpoly K x)) (r : commutant x) (a : primaryFactors x)
    (v : primaryComponent x (a : K[X])) :
    ((commutantEquivPi hx r a v : primaryComponent x (a : K[X])) : V) = r.1 (v : V) := rfl


instance [FiniteDimensional K V] (a : primaryFactors x) : Fact (Irreducible (a : K[X])) :=
  ⟨irreducible_of_mem_primaryFactors a.2⟩

noncomputable abbrev primaryMultiplicity (x : Module.End K V) (a : K[X]) : ℕ :=
  Module.finrank (AdjoinRoot a) (primaryComponent x a)

@[expose] noncomputable def commutantEquivMatrix [FiniteDimensional K V]
    (hx : Squarefree (minpoly K x)) :
    commutant x ≃ₐ[K] ((a : primaryFactors x) →
      Matrix (Fin (primaryMultiplicity x (a : K[X]))) (Fin (primaryMultiplicity x (a : K[X])))
        (AdjoinRoot (a : K[X]))) :=
  (commutantEquivPi hx).trans (AlgEquiv.piCongrRight fun a =>
    (LinearMap.toMatrixAlgEquiv (Module.finBasis (AdjoinRoot (a : K[X]))
      (primaryComponent x (a : K[X])))).restrictScalars K)


theorem finrank_eq_sum_primaryComponent [FiniteDimensional K V] (hx : Squarefree (minpoly K x)) :
    Module.finrank K V = ∑ a : primaryFactors x, Module.finrank K (primaryComponent x a) := by
  rw [(primaryEquivPi hx).finrank_eq, Module.finrank_pi_fintype]

theorem finrank_eq_sum_degree_mul_multiplicity [FiniteDimensional K V]
    (hx : Squarefree (minpoly K x)) :
    Module.finrank K V =
      ∑ a : primaryFactors x, (a : K[X]).natDegree * primaryMultiplicity x (a : K[X]) := by
  rw [finrank_eq_sum_primaryComponent hx]
  exact Finset.sum_congr rfl fun a _ => finrank_primaryComponent x (a : K[X])

theorem primaryComponent_ne_bot [FiniteDimensional K V] (hx : Squarefree (minpoly K x))
    {a : K[X]} (ha : a ∈ primaryFactors x) : primaryComponent x a ≠ ⊥ := by
  classical
  intro hbot
  set q : K[X] := ∏ b ∈ (primaryFactors x).erase a, b with hq
  have hμ : minpoly K x = a * q := by
    rw [← prod_primaryFactors hx, ← Finset.mul_prod_erase _ _ ha]
  have hqm : q.Monic := monic_prod_of_monic _ _ fun b hb =>
    monic_of_mem_primaryFactors (Finset.mem_of_mem_erase hb)
  have hinj : Function.Injective (aeval x a) := by
    rw [← LinearMap.ker_eq_bot]
    exact hbot
  have hq0 : aeval x q = 0 := by
    ext v
    apply hinj
    have : aeval x (a * q) v = 0 := by rw [← hμ, minpoly.aeval]; rfl
    rw [map_mul, Module.End.mul_apply] at this
    simpa using this
  obtain ⟨c, hc⟩ := minpoly.dvd K x hq0
  have h1 : a * c = 1 := by
    have h2 : q * (a * c) = q * 1 := by
      calc q * (a * c) = (a * q) * c := by ring
        _ = q := by rw [← hμ]; exact hc.symm
        _ = q * 1 := (mul_one q).symm
    exact mul_left_cancel₀ hqm.ne_zero h2
  exact (irreducible_of_mem_primaryFactors ha).not_isUnit (IsUnit.of_mul_eq_one c h1)


theorem exists_smul_of_forall_commute {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (γ : Module.End E W) (h : ∀ δ : Module.End E W, Commute γ δ) :
    ∃ c : E, ∀ w, γ w = c • w := by
  classical
  let b := Module.finBasis E W
  let φ := LinearMap.toMatrixAlgEquiv b
  have hM : φ γ ∈ Set.range (Matrix.scalar (Fin (Module.finrank E W))) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro i j _
    have h1 := (h (φ.symm (Matrix.single i j 1))).map φ.toRingEquiv.toRingHom
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_toRingEquiv,
      AlgEquiv.apply_symm_apply] at h1
    exact h1.symm
  obtain ⟨c, hc⟩ := hM
  refine ⟨c, fun w => ?_⟩
  have h2 : γ = c • (1 : Module.End E W) := by
    apply φ.injective
    rw [← hc, map_smul, map_one]
    simp [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  rw [h2]
  simp

theorem mem_center_commutant_iff [FiniteDimensional K V] (hx : Squarefree (minpoly K x))
    (z : commutant x) :
    z ∈ Subalgebra.center K (commutant x) ↔
      ∀ a : primaryFactors x, ∃ c : AdjoinRoot (a : K[X]),
        ∀ v : primaryComponent x (a : K[X]),
          z.1 (v : V) = ((c • v : primaryComponent x (a : K[X])) : V) := by
  classical
  constructor
  · intro hz a
    have hcomm : ∀ δ : Module.End (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X])),
        Commute (commutantEquivPi hx z a) δ := by
      intro δ
      obtain ⟨r, hr⟩ := (commutantEquivPi hx).surjective (Pi.single a δ)
      have h1 := congrArg (fun r => commutantEquivPi hx r a)
        ((Subalgebra.mem_center_iff.mp hz) r)
      simp only [map_mul, Pi.mul_apply, hr, Pi.single_eq_same] at h1
      exact h1.symm
    obtain ⟨c, hc⟩ := exists_smul_of_forall_commute _ hcomm
    exact ⟨c, fun v => by
      have := congrArg (fun y : primaryComponent x (a : K[X]) => (y : V)) (hc v)
      exact this⟩
  · intro h
    rw [Subalgebra.mem_center_iff]
    intro r
    apply Subtype.ext
    refine ext_primaryComponent hx (fun a ha v hv => ?_)
    obtain ⟨c, hc⟩ := h ⟨a, ha⟩
    have h1 := hc ⟨v, hv⟩
    have h2 := hc ⟨r.1 v, apply_mem_primaryComponent ((mem_commutant x).mp r.2) hv⟩
    have h3 : (commutantRestrict a r (c • ⟨v, hv⟩) : primaryComponent x a) =
        c • commutantRestrict a r ⟨v, hv⟩ := map_smul _ _ _
    change r.1 (z.1 v) = z.1 (r.1 v)
    calc r.1 (z.1 v) = r.1 ((c • (⟨v, hv⟩ : primaryComponent x a) : primaryComponent x a) : V) := by
          rw [h1]
      _ = ((commutantRestrict a r (c • ⟨v, hv⟩) : primaryComponent x a) : V) := rfl
      _ = ((c • commutantRestrict a r ⟨v, hv⟩ : primaryComponent x a) : V) :=
          congrArg (fun y : primaryComponent x a => (y : V)) h3
      _ = z.1 (r.1 v) := h2.symm


theorem primaryProjection_mem_commutant (x : Module.End K V) (a : K[X]) :
    primaryProjection x a ∈ commutant x :=
  (mem_commutant x).mpr (commute_aeval (Commute.refl x) _).symm

@[expose] noncomputable def commutantUnitsEquivPi [FiniteDimensional K V]
    (hx : Squarefree (minpoly K x)) :
    (commutant x)ˣ ≃* ((a : primaryFactors x) →
      (Module.End (AdjoinRoot (a : K[X])) (primaryComponent x (a : K[X])))ˣ) :=
  (Units.mapEquiv (commutantEquivPi hx).toMulEquiv).trans MulEquiv.piUnits

end Commutant

theorem squarefree_minpoly_of_aeval_eq_zero [FiniteDimensional K V] {x : Module.End K V}
    {p : K[X]} (hp : Squarefree p) (hxp : aeval x p = 0) : Squarefree (minpoly K x) :=
  hp.squarefree_of_dvd (minpoly.dvd K x hxp)

end CFSG.RankThree.PartOne.KCPrimary

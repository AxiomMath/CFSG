module

public import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryHermitian
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDual
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial

section Adjoint

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem eq_zero_of_forall_left (hB : B.IsSymm) (hBl : B.SeparatingLeft) {w : V}
    (h : ∀ v, B v w = 0) : w = 0 :=
  hBl w fun v => (hB.eq_iff).mp (h v)

theorem exists_hermAdjoint (hB : B.IsSymm) (hBl : B.SeparatingLeft) (r : Module.End K V) :
    ∃ r' : Module.End K V, ∀ v w, B (r v) w = B v (r' w) := by
  classical
  let b := Module.finBasis K V
  let Φ : V →ₗ[K] (Fin (Module.finrank K V) → K) := LinearMap.pi fun i => B (b i)
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    refine eq_zero_of_forall_left hB hBl fun v => ?_
    have hi : ∀ i, B (b i) w = 0 := fun i => congrFun hw i
    rw [← b.sum_repr v, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply, hi i, smul_zero]
  have hΦb : Function.Bijective Φ :=
    ⟨hΦ, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simp)).mp hΦ⟩
  let Φe := LinearEquiv.ofBijective Φ hΦb
  let b' : Fin (Module.finrank K V) → V := fun i => Φe.symm (Pi.single i 1)
  have hbb' : ∀ i j, B (b i) (b' j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (Φe.apply_symm_apply (Pi.single j 1)) i
    change B (b i) (Φe.symm (Pi.single j 1)) = _ at this
    exact this.trans (by simp [Pi.single_apply])
  have hexp : ∀ v, v = ∑ i, B (b i) v • b' i := by
    intro v
    have h1 : Φe v = ∑ i, B (b i) v • Pi.single i (1 : K) := by
      funext j
      simp [Φe, Φ, Finset.sum_apply, Pi.single_apply]
    calc v = Φe.symm (Φe v) := (Φe.symm_apply_apply v).symm
      _ = ∑ i, B (b i) v • b' i := by rw [h1, map_sum]; simp [b', map_smul]
  refine ⟨∑ i, (B (r (b' i))).smulRight (b i), fun v w => ?_⟩
  have hrv : r v = ∑ i, B (b i) v • r (b' i) := by
    conv_lhs => rw [hexp v]
    rw [map_sum]
    simp [map_smul]
  rw [hrv, map_sum, LinearMap.sum_apply]
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, LinearMap.sum_apply,
    LinearMap.smulRight_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hB.eq, mul_comm]
  rfl


variable (hB : B.IsSymm) (hBl : B.SeparatingLeft)
include hB hBl

@[expose] noncomputable def hermAdjoint (r : Module.End K V) : Module.End K V :=
  (exists_hermAdjoint hB hBl r).choose

theorem hermAdjoint_spec (r : Module.End K V) (v w : V) :
    B (r v) w = B v (hermAdjoint hB hBl r w) :=
  (exists_hermAdjoint hB hBl r).choose_spec v w

theorem hermAdjoint_unique {r s : Module.End K V} (h : ∀ v w, B (r v) w = B v (s w)) :
    s = hermAdjoint hB hBl r := by
  ext w
  refine sub_eq_zero.mp (eq_zero_of_forall_left hB hBl fun v => ?_)
  rw [map_sub, ← h, ← hermAdjoint_spec]
  simp

theorem hermAdjoint_spec' (r : Module.End K V) (v w : V) :
    B (hermAdjoint hB hBl r v) w = B v (r w) := by
  rw [← hB.eq, ← hermAdjoint_spec hB hBl, hB.eq]

@[simp] theorem hermAdjoint_hermAdjoint (r : Module.End K V) :
    hermAdjoint hB hBl (hermAdjoint hB hBl r) = r :=
  (hermAdjoint_unique hB hBl (hermAdjoint_spec' hB hBl r)).symm

theorem hermAdjoint_mul (r s : Module.End K V) :
    hermAdjoint hB hBl (r * s) = hermAdjoint hB hBl s * hermAdjoint hB hBl r :=
  (hermAdjoint_unique hB hBl fun v w => by
    rw [Module.End.mul_apply, hermAdjoint_spec hB hBl r, hermAdjoint_spec hB hBl s,
      Module.End.mul_apply]).symm

@[simp] theorem hermAdjoint_one : hermAdjoint hB hBl (1 : Module.End K V) = 1 :=
  (hermAdjoint_unique hB hBl fun _ _ => rfl).symm

theorem hermAdjoint_add (r s : Module.End K V) :
    hermAdjoint hB hBl (r + s) = hermAdjoint hB hBl r + hermAdjoint hB hBl s :=
  (hermAdjoint_unique hB hBl fun v w => by
    have h1 := hermAdjoint_spec hB hBl r v w
    have h2 := hermAdjoint_spec hB hBl s v w
    simp only [LinearMap.add_apply, map_add, h1, h2]).symm

theorem hermAdjoint_smul (c : K) (r : Module.End K V) :
    hermAdjoint hB hBl (c • r) = σ c • hermAdjoint hB hBl r :=
  (hermAdjoint_unique hB hBl fun v w => by
    have h1 := hermAdjoint_spec hB hBl r v w
    simp only [LinearMap.smul_apply, map_smulₛₗ, h1, smul_eq_mul, RingHom.id_apply]).symm

theorem hermAdjoint_pow (r : Module.End K V) (n : ℕ) :
    hermAdjoint hB hBl (r ^ n) = hermAdjoint hB hBl r ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, hermAdjoint_mul, ih, pow_succ']


theorem hermAdjoint_of_mem_sesqUnitaryGroup {u : LinearMap.GeneralLinearGroup K V}
    (hu : u ∈ sesqUnitaryGroup B) :
    hermAdjoint hB hBl (u : Module.End K V) =
      ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) := by
  symm
  apply hermAdjoint_unique
  intro v w
  have h1 := hu v (((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) w)
  have h2 : (u : Module.End K V) (((u⁻¹ : LinearMap.GeneralLinearGroup K V) :
      Module.End K V) w) = w := by
    rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
    rfl
  rw [h2] at h1
  exact h1

theorem hermAdjoint_aeval {u : LinearMap.GeneralLinearGroup K V} (hu : u ∈ sesqUnitaryGroup B)
    (f : K[X]) :
    hermAdjoint hB hBl (aeval (u : Module.End K V) f) =
      aeval ((u⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) (f.map σ) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, hermAdjoint_add, hp, hq, Polynomial.map_add, map_add]
  | monomial n c =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, smul_mul_assoc, one_mul, one_mul,
      hermAdjoint_smul, hermAdjoint_pow, hermAdjoint_of_mem_sesqUnitaryGroup hB hBl hu]

theorem aeval_dualPoly {u : LinearMap.GeneralLinearGroup K V} (hu : u ∈ sesqUnitaryGroup B)
    (a : K[X]) :
    aeval (u : Module.End K V) (dualPoly σ a) =
      (σ (a.coeff 0))⁻¹ • ((u : Module.End K V) ^ a.natDegree *
        hermAdjoint hB hBl (aeval (u : Module.End K V) a)) := by
  rw [dualPoly, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    reverse, aeval_reflect_of_unit u _ le_rfl, hermAdjoint_aeval hB hBl hu, natDegree_map]

end Adjoint

end CFSG.RankThree.PartOne.KCUnitary

module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryCentralizer

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryRegular CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

variable {ℓ f n p : ℕ} {K : Type} [Field K]

structure LiftData (h : UnitaryFieldData ℓ f K) (n p : ℕ) (x : gramSU h (idGram K n)) : Prop where
  three_le : 3 ≤ n
  four_le : 3 < ℓ ^ f
  prime : p.Prime
  ne_char : p ≠ ℓ
  noTorsion : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1
  pow_eq_one : x ^ p = 1

variable {h : UnitaryFieldData ℓ f K} {x : gramSU h (idGram K n)}

@[expose] def liftUnitary (x : gramSU h (idGram K n)) : primeFormUnitary h (idGram K n) :=
  ⟨x, x.2.1⟩

theorem primeFormConjHom_liftUnitary (x : gramSU h (idGram K n)) :
    primeFormConjHom h (idGram K n) (liftUnitary x) = MulAut.conj (x : primeFormP h (idGram K n)) :=
  primeFormConjHom_eq_conj h _ x

namespace LiftData

variable (L : LiftData h n p x)

include L in
theorem squarefree_minpoly :
    Squarefree (minpoly K ((toLinU h n (liftUnitary x) : LinearMap.GeneralLinearGroup K
      (Fin n → K)) : Module.End K (Fin n → K))) := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hp0 : (p : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h0
    exact L.ne_char ((Nat.prime_dvd_prime_iff_eq h.prime L.prime).mp this).symm
  have hsep : (Polynomial.X ^ p - Polynomial.C (1 : K)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 hp0 one_ne_zero
  refine squarefree_minpoly_of_aeval_eq_zero (p := Polynomial.X ^ p - Polynomial.C (1 : K))
    hsep.squarefree ?_
  have hxp : (toLinU h n (liftUnitary x)) ^ p = 1 := by
    rw [← map_pow]
    have : (liftUnitary x) ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact congrArg Subtype.val L.pow_eq_one)
    rw [this, map_one]
  have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
    (g : Module.End K (Fin n → K))) hxp
  simp only [Units.val_pow_eq_pow_val, Units.val_one] at h2
  simp [h2]

include L in
theorem commute_of_conj_commute (A : primeFormUnitary h (idGram K n))
    (hA : primeFormConjHom h (idGram K n) (liftUnitary x) * primeFormConjHom h (idGram K n) A =
      primeFormConjHom h (idGram K n) A * primeFormConjHom h (idGram K n) (liftUnitary x)) :
    A * liftUnitary x = liftUnitary x * A := by
  set x' := liftUnitary x with hx'
  have hρ : primeFormConjHom h (idGram K n) (A * x') =
      primeFormConjHom h (idGram K n) (x' * A) := by
    rw [map_mul, map_mul]
    exact hA.symm
  have hz1 : primeFormConjHom h (idGram K n) ((x' * A)⁻¹ * (A * x')) = 1 := by
    rw [map_mul, map_inv, hρ, inv_mul_cancel]
  obtain ⟨c, hc, hzc⟩ := (primeFormConjHom_eq_one_iff L.three_le L.four_le _).mp hz1
  have hzc' : ((x' : GL (Fin n) K) * (A : GL (Fin n) K))⁻¹ * ((A : GL (Fin n) K) * x') =
      GeneralLinearGroup.scalar (Fin n) c := by
    simpa using hzc
  have e : (A : GL (Fin n) K) * x' =
      (x' : GL (Fin n) K) * A * GeneralLinearGroup.scalar (Fin n) c := by
    rw [← hzc', mul_inv_cancel_left]
  have hcA : (A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c =
      GeneralLinearGroup.scalar (Fin n) c * (A : GL (Fin n) K) := (commute_scalar c _).eq
  have hconj : (A : GL (Fin n) K) * x' * (A : GL (Fin n) K)⁻¹ =
      (x' : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by
    calc (A : GL (Fin n) K) * x' * (A : GL (Fin n) K)⁻¹
        = (x' : GL (Fin n) K) * A * GeneralLinearGroup.scalar (Fin n) c *
          (A : GL (Fin n) K)⁻¹ := by rw [e]
      _ = (x' : GL (Fin n) K) * ((A : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c) *
          (A : GL (Fin n) K)⁻¹ := by group
      _ = (x' : GL (Fin n) K) * (GeneralLinearGroup.scalar (Fin n) c * (A : GL (Fin n) K)) *
          (A : GL (Fin n) K)⁻¹ := by rw [hcA]
      _ = (x' : GL (Fin n) K) * GeneralLinearGroup.scalar (Fin n) c := by group
  have hx'p : (x' : GL (Fin n) K) ^ p = 1 := by
    have : (x : GL (Fin n) K) ^ p = 1 := by
      have := congrArg (fun y : gramSU h (idGram K n) => (y : GL (Fin n) K)) L.pow_eq_one
      simpa using this
    exact this
  have hcp : c ^ p = 1 := by
    have h1 : ((A : GL (Fin n) K) * x' * (A : GL (Fin n) K)⁻¹) ^ p = 1 := by
      rw [conj_pow, hx'p, mul_one, mul_inv_cancel]
    rw [hconj, ((commute_scalar c (x' : GL (Fin n) K)).symm.symm).mul_pow, hx'p, one_mul,
      ← map_pow] at h1
    exact (scalar_eq_one_iff (by have := L.three_le; omega)).mp h1
  have hcn : c ^ n = 1 := by
    have hdet := congrArg (Matrix.GeneralLinearGroup.det) hconj
    have hx1 : Matrix.GeneralLinearGroup.det (x' : GL (Fin n) K) = 1 := Units.ext x.2.2
    simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] at hdet
    rw [mul_comm (Matrix.GeneralLinearGroup.det (A : GL (Fin n) K)), mul_assoc, mul_inv_cancel,
      mul_one, hx1, one_mul] at hdet
    exact hdet.symm
  have hc1 : c = 1 := L.noTorsion c ((pow_succ_eq_one_iff_norm h c).mp hc) hcn hcp
  rw [hc1, map_one, mul_one] at hconj
  have : (A : GL (Fin n) K) * x' = (x' : GL (Fin n) K) * A := by
    calc (A : GL (Fin n) K) * x' = (A * x' * (A : GL (Fin n) K)⁻¹) * A := by group
      _ = (x' : GL (Fin n) K) * A := by rw [hconj]
  exact Subtype.ext this

include L in
theorem centralizer_image :
    primeFormD h (idGram K n) ⊓ Subgroup.centralizer
        ({primeFormConjHom h (idGram K n) (liftUnitary x)} :
          Set (MulAut (primeFormP h (idGram K n)))) =
      (Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n)))).map
        (primeFormConjHom h (idGram K n)) := by
  ext d
  constructor
  · rintro ⟨⟨A, rfl⟩, hd⟩
    refine ⟨A, ?_, rfl⟩
    have hd' := Subgroup.mem_centralizer_singleton_iff.mp hd
    exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_conj_commute L A hd'.symm)
  · rintro ⟨A, hA, rfl⟩
    refine ⟨⟨A, rfl⟩, ?_⟩
    have hA' := Subgroup.mem_centralizer_singleton_iff.mp hA
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, hA']

end LiftData

theorem centralizer_eq_comap_unitaryCentralizer (x : gramSU h (idGram K n)) :
    Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))) =
      (unitaryCentralizer (idForm h n) (toLinU h n (liftUnitary x))).comap (toLinU h n) := by
  ext A
  rw [Subgroup.mem_comap, mem_unitaryCentralizer]
  refine ⟨fun hA => ⟨toLinU_mem A, ?_⟩, fun hA => ?_⟩
  · have hA' := Subgroup.mem_centralizer_singleton_iff.mp hA
    have := congrArg (toLinU h n) hA'
    rw [map_mul, map_mul] at this
    have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup K (Fin n → K) =>
      (g : Module.End K (Fin n → K))) this
    exact h2
  · have h1 : toLinU h n (A * liftUnitary x) = toLinU h n (liftUnitary x * A) := by
      rw [map_mul, map_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact hA.2.eq
    exact Subgroup.mem_centralizer_singleton_iff.mpr (toLinU_injective h1)

end CFSG.RankThree.PartOne.KCUnitaryModel

module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeCentralizer

public section

namespace CFSG.RankThree.PartOne.KCUnitaryModel

open Polynomial Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryRegular
  CFSG.RankThree.PartOne.KCPrimary
open scoped commutatorElement

variable {ℓ f n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem primeFormConjHom_eq_one_iff_of_ne (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (A : primeFormUnitary h (idGram K n)) :
    primeFormConjHom h (idGram K n) A = 1 ↔ A ∈ idScalarKernel h n := by
  have key := (unitary_prime_form_full_semilinear_realization h
    (isPrimeFormGram_idGram (K := K) (n := n)) hn hne).2.2.1 ⟨A, 1⟩
  rw [primeFormPsi_apply, map_one, mul_one] at key
  rw [key]
  constructor
  · rintro ⟨-, c, hc, hA⟩
    exact ⟨c, (pow_succ_eq_one_iff_norm h c).mpr hc, hA⟩
  · rintro ⟨c, hc, hA⟩
    exact ⟨rfl, c, (pow_succ_eq_one_iff_norm h c).mp hc, hA⟩

theorem commute_of_mem_ker_of_ne (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {z : primeFormUnitary h (idGram K n)} (hz : primeFormConjHom h (idGram K n) z = 1)
    (g : primeFormUnitary h (idGram K n)) : Commute z g := by
  obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff_of_ne hn hne z).mp hz
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hc]
  exact (commute_scalar c (g : GL (Fin n) K)).symm.eq

structure PlaneData (h : UnitaryFieldData ℓ f K) (n p : ℕ) (x : gramSU h (idGram K n)) : Prop where
  three_le : 3 ≤ n
  ne : ¬(n = 3 ∧ ℓ ^ f = 2)
  prime : p.Prime
  ne_char : p ≠ ℓ
  noTorsion : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1
  pow_eq_one : x ^ p = 1

namespace PlaneData

variable {x : gramSU h (idGram K n)} (L : PlaneData h n p x)

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
theorem primaryData : UnitaryPrimaryData h.bar (idForm h n) (toLinU h n (liftUnitary x)) :=
  ⟨h.bar_bar, idForm_isSymm h n, idForm_separatingLeft h n, toLinU_mem _, L.squarefree_minpoly⟩

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
  obtain ⟨c, hc, hzc⟩ := (primeFormConjHom_eq_one_iff_of_ne L.three_le L.ne _).mp hz1
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
theorem centralizer_image_SU :
    ((gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n))).map
        (primeFormConjHom h (idGram K n)) ⊓
      Subgroup.centralizer ({primeFormConjHom h (idGram K n) (liftUnitary x)} :
        Set (MulAut (primeFormP h (idGram K n)))) =
    (Subgroup.centralizer ({liftUnitary x} : Set (primeFormUnitary h (idGram K n))) ⊓
      (gramSU h (idGram K n)).subgroupOf (primeFormUnitary h (idGram K n))).map
        (primeFormConjHom h (idGram K n)) := by
  ext d
  constructor
  · rintro ⟨⟨A, hA, rfl⟩, hd⟩
    refine ⟨A, ⟨?_, hA⟩, rfl⟩
    have hd' := Subgroup.mem_centralizer_singleton_iff.mp hd
    exact Subgroup.mem_centralizer_singleton_iff.mpr (L.commute_of_conj_commute A hd'.symm)
  · rintro ⟨A, ⟨hAc, hA⟩, rfl⟩
    refine ⟨⟨A, hA, rfl⟩, ?_⟩
    have hA' := Subgroup.mem_centralizer_singleton_iff.mp hAc
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, hA']

end PlaneData

end CFSG.RankThree.PartOne.KCUnitaryModel

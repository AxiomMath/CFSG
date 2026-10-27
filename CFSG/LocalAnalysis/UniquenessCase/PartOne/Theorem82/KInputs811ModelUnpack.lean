module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.WeirSylow.CrossRankForms
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import CFSG.Open.StatedAPI
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpack

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem not_dvd_card_scalars_of_not_dvd_card_sub_one {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K - 1)
    (M : Subgroup (GL ι K)) [Finite M] :
    ¬ p ∣ Nat.card ((StatedScalars ι K).subgroupOf M) :=
  StatedAPI.not_dvd_card_statedScalars_subgroupOf M hp hpK fun c _ => by
    have h := pow_card_eq_one' (G := Kˣ) (x := c)
    rwa [Nat.card_units] at h

theorem not_dvd_card_scalars_of_dvd_card {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K)
    (M : Subgroup (GL ι K)) [Finite M] :
    ¬ p ∣ Nat.card ((StatedScalars ι K).subgroupOf M) :=
  not_dvd_card_scalars_of_not_dvd_card_sub_one hp (fun h => hp.one_lt.ne' (by
    have h1 := Nat.dvd_sub hpK h
    rwa [Nat.sub_sub_self Nat.card_pos, Nat.dvd_one] at h1)) M

theorem not_dvd_card_scalars_statedSp {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) :=
  StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSp n K) hp
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h))
    (fun c hc => (StatedAPI.scalar_mem_statedSp_iff hn c).1 hc)

theorem not_dvd_card_scalars_statedOmega_quadOdd {n : ℕ} {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n ⊕ Fin n ⊕ Unit) K).subgroupOf
      (StatedOmega (StatedQuadOdd n K))) :=
  StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedOmega (StatedQuadOdd n K)) hp
    (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h))
    (fun c hc => CFSG.GroupTheory.WeirSylow.sq_eq_one_of_scalar_mem_statedOmega_quadOdd c hc)

theorem not_dvd_card_scalars_statedOmega_quadMinus {K : Type} [Field K] [Finite K] (b c : K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 4 K b c))) := by
  open CFSG.LieType.Universal.Spin in
  refine StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedOmega (StatedQuadMinus 4 K b c))
    hp (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h))
    (fun a ha => CFSG.GroupTheory.WeirSylow.sq_eq_one_of_scalar_mem_statedOmega
      (w := Pi.single (.inr (.inr 0)) 1) ?_ ?_ ha)
  · intro a v
    rw [← coe_quadMinus 4 K b c, QuadraticMap.map_smul, smul_eq_mul, sq]
  · simp [StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]

theorem not_dvd_card_scalars_statedSL {n : ℕ} {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) :
    ¬ p ∣ Nat.card ((StatedScalars (Fin n) K).subgroupOf (StatedSL n K)) :=
  StatedAPI.not_dvd_card_statedScalars_subgroupOf (StatedSL n K) hp hpn fun c hc => by
    have h := StatedAPI.det_of_mem_statedSL hc
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact Units.val_eq_one.1 (by rw [Units.val_pow_eq_pow_val]; exact h)

theorem isCyclic_scalars_subgroupOf {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] (M : Subgroup (GL ι K)) : IsCyclic ((StatedScalars ι K).subgroupOf M) := by
  haveI : IsCyclic (StatedScalars ι K) :=
    isCyclic_of_surjective (Matrix.GeneralLinearGroup.scalar ι : Kˣ →* GL ι K).rangeRestrict
      (MonoidHom.rangeRestrict_surjective _)
  refine isCyclic_of_injective
    (((M.subtype.comp ((StatedScalars ι K).subgroupOf M).subtype).codRestrict (StatedScalars ι K)
      fun x => x.2)) ?_
  intro x y h
  have := congrArg (fun z : StatedScalars ι K => (z : GL ι K)) h
  exact Subtype.ext (Subtype.ext this)

theorem three_ne_zero_of_charP {K : Type} [Field K] {r : ℕ} [CharP K r] (hr : r.Prime)
    (hr3 : r ≠ 3) : (3 : K) ≠ 0 := fun h =>
  hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
    ((CharP.cast_eq_zero_iff K r 3).1 (by exact_mod_cast h)))

theorem two_ne_zero_of_charP {K : Type} [Field K] {r : ℕ} [CharP K r] (hr : r.Prime)
    (hr2 : r ≠ 2) : (2 : K) ≠ 0 := fun h =>
  hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
    ((CharP.cast_eq_zero_iff K r 2).1 (by exact_mod_cast h)))

private theorem charP_of_card_eq_pow {K : Type} [Field K] [Finite K] {r m : ℕ} (hr : r.Prime)
    (hK : Nat.card K = r ^ m) : CharP K r := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card, hK])

private theorem not_three_dvd_pow {r f : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) : ¬ 3 ∣ r ^ f := fun h3 =>
  hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).1 (Nat.prime_three.dvd_of_dvd_pow h3)).symm

theorem exists_model_of_lieModel_psp {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .PSp 3 r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K r), Nat.card K = r ^ f ∧
      ¬ 3 ∣ Nat.card K ∧ Nonempty (X ≃* StatedProj (StatedSp 3 K)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hr : r.Prime := hadm.1
  exact ⟨K, inferInstance, inferInstance, charP_of_card_eq_pow hr hK, hK,
    by rw [hK]; exact not_three_dvd_pow hr hr3, ⟨e⟩⟩

theorem exists_model_of_lieModel_pomegaOdd {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaOdd 3 r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K r), Nat.card K = r ^ f ∧
      Odd (Nat.card K) ∧ ¬ 3 ∣ Nat.card K ∧
      Nonempty (X ≃* StatedProj (StatedOmega (StatedQuadOdd 3 K))) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hr : r.Prime := hadm.1
  refine ⟨K, inferInstance, inferInstance, charP_of_card_eq_pow hr hK, hK, ?_, ?_, ⟨e⟩⟩
  · rw [hK]
    exact (hr.odd_of_ne_two hadm.2.2.2).pow
  · rw [hK]
    exact not_three_dvd_pow hr hr3

theorem exists_model_of_lieModel_pomegaMinus {X : Type} [Group X] {r f : ℕ} (hr3 : r ≠ 3)
    (h : LieModel X .POmegaMinus 4 r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K r), Nat.card K = r ^ f ∧
      ¬ 3 ∣ Nat.card K ∧ ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (X ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) := by
  obtain ⟨hadm, K, _, _, hK, b, c, hbc, ⟨e⟩⟩ := h.statedClassicalModel (by decide)
  have hr : r.Prime := hadm.1
  exact ⟨K, inferInstance, inferInstance, charP_of_card_eq_pow hr hK, hK,
    by rw [hK]; exact not_three_dvd_pow hr hr3, b, c, hbc, ⟨e⟩⟩

theorem exists_model_of_lieModel_psl {X : Type} [Group X] {n r f : ℕ} (hn : n ≠ 0)
    (h : LieModel X .PSL n r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K r), Nat.card K = r ^ f ∧
      Nonempty (X ≃* StatedProj (StatedSL n K)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero hn
  exact ⟨K, inferInstance, inferInstance, charP_of_card_eq_pow hadm.1 hK, hK, ⟨e⟩⟩

theorem exists_model_of_lieModel_psu {X : Type} [Group X] {n r f : ℕ} (hn : n ≠ 0)
    (h : LieModel X .PSU n r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K r), Nat.card K = (r ^ f) ^ 2 ∧
      Nonempty (X ≃* StatedProj (StatedSU n (r ^ f) K)) := by
  obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := h.statedClassicalModel_of_ne_zero hn
  exact ⟨K, inferInstance, inferInstance,
    charP_of_card_eq_pow hadm.1 (m := 2 * f) (by rw [hK, ← pow_mul, mul_comm]), hK, ⟨e⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpack

module

public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.UniqueElemSylow
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.LieType.Universal.Unitary.Basic
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Unitary.SUnThreeLocalTransport
import CFSG.GroupTheory.WeirSylow.UniqueE27Unitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811ModelUnpack
import CFSG.Open.StatedAPI
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpackSU

open CFSG.Open CFSG.GroupTheory CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.Blueprint (LieModel)

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem pow_succ_eq_one_of_scalar_mem_SU {n : ℕ} (hn : 1 ≤ n) (c : Fˣ)
    (hc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ SU (unitaryInvolution F p f) n) :
    c ^ (p ^ f + 1) = 1 := by
  have h := (mem_SU.1 hc).2
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, conjTr] at h
  have h1 := congrFun (congrFun h ⟨0, hn⟩) (Fin.rev ⟨0, hn⟩)
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    antidiag, Matrix.of_apply, unitaryInvolution_apply] at h1
  refine Units.val_eq_one.1 ?_
  rw [Units.val_pow_eq_pow_val, pow_succ]
  simpa using h1

theorem not_dvd_card_scalars_SU {n : ℕ} (hn : 1 ≤ n) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓq : ¬ ℓ ∣ p ^ f + 1) :
    ¬ ℓ ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (SU (unitaryInvolution F p f) n)) :=
  StatedAPI.not_dvd_card_statedScalars_subgroupOf (SU (unitaryInvolution F p f) n) hℓ hℓq
    fun c hc => pow_succ_eq_one_of_scalar_mem_SU hn c hc

theorem not_dvd_card_scalars_SU_of_not_dvd {n : ℕ} {σ : F ≃+* F} {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓn : ¬ ℓ ∣ n) :
    ¬ ℓ ∣ Nat.card ((StatedScalars (Fin n) F).subgroupOf (SU σ n)) :=
  StatedAPI.not_dvd_card_statedScalars_subgroupOf (SU σ n) hℓ hℓn fun c hc => by
    have h := (mem_SU.1 hc).1
    rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact Units.val_eq_one.1 (by rw [Units.val_pow_eq_pow_val]; exact h)

theorem uniqueElemSylow_statedProj_SU (hF : Nat.card F = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1)
    {n : ℕ} (hn : n = 6 ∨ n = 7) :
    UniqueElemSylow 3 3 (StatedProj (SU (unitaryInvolution F p f) n)) := by
  obtain ⟨e⟩ := CFSG.ClassicalGroups.SUnThreeLocal.statedProj_statedSU_mulEquiv_SU_of_card hF n
  exact UniqueElemSylow.of_mulEquiv e
    (CFSG.GroupTheory.WeirSylow.uniqueElemSylow_statedProj_statedSU_of_mod_three_eq_one F hF hq hn)

variable {X : Type} [Group X] {n r f : ℕ}

theorem exists_model_of_lieModel_psu_SU [Fact r.Prime] (hn : n ≠ 0) (h : LieModel X .PSU n r f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K r), Nat.card K = (r ^ f) ^ 2 ∧
      Nonempty (X ≃* StatedProj (SU (unitaryInvolution K r f) n)) := by
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := ModelUnpack.exists_model_of_lieModel_psu hn h
  obtain ⟨e'⟩ := CFSG.ClassicalGroups.SUnThreeLocal.statedProj_statedSU_mulEquiv_SU_of_card hK n
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, ⟨e.trans e'⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.ModelUnpackSU

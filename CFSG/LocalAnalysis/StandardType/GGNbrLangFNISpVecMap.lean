module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType.ClassicalBlocks

open CFSG.Open (StatedSp)
open CFSG.RankThree.Classical
open Matrix

@[expose] def vecMap {ι K : Type*} [Field K] (σ : K ≃+* K) : (ι → K) ≃+ (ι → K) :=
  AddEquiv.piCongrRight fun _ => σ.toAddEquiv

@[simp] theorem vecMap_apply {ι K : Type*} [Field K] (σ : K ≃+* K) (v : ι → K) (i : ι) :
    vecMap σ v i = σ (v i) := rfl

@[simp] theorem vecMap_symm_apply {ι K : Type*} [Field K] (σ : K ≃+* K) (v : ι → K) (i : ι) :
    (vecMap σ).symm v i = σ.symm (v i) := rfl

theorem vecMap_smul {ι K : Type*} [Field K] (σ : K ≃+* K) (c : K) (v : ι → K) :
    vecMap σ (c • v) = σ c • vecMap σ v := by
  ext i
  simp [Pi.smul_apply, map_mul]

theorem map_mulVec_eq_vecMap {ι K : Type*} [Fintype ι] [Field K] (σ : K ≃+* K)
    (M : Matrix ι ι K) (v : ι → K) :
    (M.map (σ : K →+* K)) *ᵥ v = vecMap σ (M *ᵥ (vecMap σ).symm v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, vecMap_apply, vecMap_symm_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [map_mul]

theorem vecMap_mulVec_of_map_eq {ι K : Type*} [Fintype ι] [Field K] (σ : K ≃+* K)
    {M : Matrix ι ι K} (hM : M.map (σ : K →+* K) = M) (v : ι → K) :
    vecMap σ (M *ᵥ v) = M *ᵥ vecMap σ v := by
  conv_rhs => rw [← hM, map_mulVec_eq_vecMap, AddEquiv.symm_apply_apply]

theorem vecMap_spEnd {K : Type} [Field K] {n : ℕ} (β : StatedSp n K) {σ : K ≃+* K}
    (hσ : Matrix.GeneralLinearGroup.map (σ : K →+* K) (β : GL (Fin n ⊕ Fin n) K) =
      (β : GL (Fin n ⊕ Fin n) K)) (v : Fin n ⊕ Fin n → K) :
    vecMap σ (spEnd β v) = spEnd β (vecMap σ v) :=
  vecMap_mulVec_of_map_eq σ (congrArg (fun z : GL (Fin n ⊕ Fin n) K =>
    (z : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) hσ) v

theorem spForm_vecMap {K : Type} [Field K] {n : ℕ} (σ : K ≃+* K) (v w : Fin n ⊕ Fin n → K) :
    spForm n K (vecMap σ v) (vecMap σ w) = σ (spForm n K v w) := by
  let J := CFSG.ClassicalInvolution.Models.SymplecticPairs.gram K n
  have hgram : J.map (σ : K →+* K) = J := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      by_cases hij : i = j <;>
        simp [J, CFSG.ClassicalInvolution.Models.SymplecticPairs.gram, Matrix.fromBlocks,
          Matrix.one_apply, hij]
  rw [spForm_apply, spForm_apply, ← vecMap_mulVec_of_map_eq σ hgram w]
  exact (RingHom.map_dotProduct (σ : K →+* K) v (J *ᵥ w)).symm

end CFSG.StandardType.ClassicalBlocks

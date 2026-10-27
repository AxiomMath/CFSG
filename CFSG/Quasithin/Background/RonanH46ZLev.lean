module

public import CFSG.Quasithin.Background.RonanH46ZBase

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem det_blkMatZ_of_perfZ {g : SL(3, K)} (hg : g ∈ perfZ K) :
    (blkMatZ (g : Matrix (Fin 3) (Fin 3) K)).det = 1 := by
  obtain ⟨h10, h20, h00⟩ := hg
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  rw [Matrix.det_fin_two]
  simp only [blkMatZ]
  simp [h10, h20, h00] at hdet ⊢
  linear_combination hdet

theorem blkMatZ_embZ (A : SL(2, K)) :
    blkMatZ (embZ A : Matrix (Fin 3) (Fin 3) K) = (A : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMatZ, embZ]

private noncomputable def slBar (n : ℕ) (A : SL(2, K)) : SL(2, K) :=
  ⟨(A : Matrix (Fin 2) (Fin 2) K).map (bar n), by
    have hd := A.2
    rw [Matrix.det_fin_two] at hd ⊢
    have := congrArg (bar n) hd
    simpa [map_sub, map_mul] using this⟩

private theorem slBar_coe (n : ℕ) (A : SL(2, K)) :
    (slBar n A : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K).map (bar n) :=
  rfl

private theorem slBar_slBar (hK : Nat.card K = (2 ^ n) ^ 2) (A : SL(2, K)) :
    (slBar n (slBar n A) : Matrix (Fin 2) (Fin 2) K) = (A : Matrix (Fin 2) (Fin 2) K) := by
  rw [slBar_coe, slBar_coe]
  ext i j
  simp [bar_bar hK]

theorem LZ_rowV2 (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)} (hy : y ∈ LZ hK) :
    ∃ A : SL(2, K), ∀ X : ↥(V2z n K), rowV2 n K ⟨y X, LZ_mem_V2z hK hy X.2⟩ =
      Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ
        Multiplicative.toAdd (rowV2 n K X)) := by
  obtain ⟨g₀, hg₀, rfl⟩ := mem_LZ hy
  refine ⟨slBar n ⟨blkMatZ (g₀ : Matrix (Fin 3) (Fin 3) K), det_blkMatZ_of_perfZ hg₀⟩,
    fun X => ?_⟩
  exact rowV2_rho hK hg₀ X

theorem exists_LZ_rowV2 (hK : Nat.card K = (2 ^ n) ^ 2) (h4 : 4 ≤ Nat.card K) (A : SL(2, K)) :
    ∃ (y : MulAut (HMod n K)) (hy : y ∈ LZ hK), ∀ X : ↥(V2z n K),
      rowV2 n K ⟨y X, LZ_mem_V2z hK hy X.2⟩ =
        Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ
          Multiplicative.toAdd (rowV2 n K X)) := by
  refine ⟨rho hK (embZ (slBar n A)), rho_embZ_mem_LZ h4 (slBar n A), fun X => ?_⟩
  have h := rowV2_rho hK (embZ_mem_perfZ (slBar n A)) X
  rw [blkMatZ_embZ, slBar_coe] at h
  have h2 : ((A : Matrix (Fin 2) (Fin 2) K).map (bar n)).map (bar n) =
      (A : Matrix (Fin 2) (Fin 2) K) := by
    have := slBar_slBar hK A
    rwa [slBar_coe, slBar_coe] at this
  rw [h2] at h
  exact h

theorem LZ_hermBlkZ (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)} (hy : y ∈ LZ hK) :
    ∃ A : SL(2, K), ∀ X : HMod n K, hermBlkZ (y X) =
      (A : Matrix (Fin 2) (Fin 2) K) * hermBlkZ X *
        ((A : Matrix (Fin 2) (Fin 2) K).map (bar n))ᵀ := by
  obtain ⟨g₀, hg₀, rfl⟩ := mem_LZ hy
  exact ⟨⟨blkMatZ (g₀ : Matrix (Fin 3) (Fin 3) K), det_blkMatZ_of_perfZ hg₀⟩,
    fun X => rhoZ_block hK hg₀ X⟩

theorem exists_LZ_hermBlkZ (hK : Nat.card K = (2 ^ n) ^ 2) (h4 : 4 ≤ Nat.card K)
    (A : SL(2, K)) :
    ∃ y ∈ LZ hK, ∀ X : HMod n K, hermBlkZ (y X) =
      (A : Matrix (Fin 2) (Fin 2) K) * hermBlkZ X *
        ((A : Matrix (Fin 2) (Fin 2) K).map (bar n))ᵀ := by
  refine ⟨rho hK (embZ A), rho_embZ_mem_LZ h4 A, fun X => ?_⟩
  rw [rhoZ_block hK (embZ_mem_perfZ A) X, blkMatZ_embZ]

end CFSG.Quasithin.RonanH46

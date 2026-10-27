module

public import CFSG.Quasithin.Background.RonanH46Irr
public import CFSG.Quasithin.Background.RonanH44Orth
public import CFSG.Quasithin.Background.RonanH46Defs

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem mem_commOnR_of {hK : Nat.card K = (2 ^ 1) ^ 2} (a : MulAut (HMod 1 K))
    (ha : a ∈ LW hK) (X : HMod 1 K) : a X * X⁻¹ ∈ commOnR ⊤ (LW hK) := by
  unfold commOnR
  exact Subgroup.subset_closure ⟨a, ha, X, Subgroup.mem_top _, rfl⟩

private def hermBlkSub (S : Subgroup (HMod 1 K)) : AddSubgroup (Matrix (Fin 2) (Fin 2) K) where
  carrier := {B | ∃ X ∈ S, hermBlk X = B}
  zero_mem' := ⟨1, S.one_mem, hermBlk_one⟩
  add_mem' := by
    rintro _ _ ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
    exact ⟨X * Y, S.mul_mem hX hY, hermBlk_mul X Y⟩
  neg_mem' := by
    rintro _ ⟨X, hX, rfl⟩
    refine ⟨X⁻¹, S.inv_mem hX, ?_⟩
    ext i j
    simp [hermBlk, mat_inv]

private theorem mem_hermBlkSub {S : Subgroup (HMod 1 K)} {B : Matrix (Fin 2) (Fin 2) K} :
    B ∈ hermBlkSub S ↔ ∃ X ∈ S, hermBlk X = B :=
  Iff.rfl

private theorem hermBlk_herm (X : HMod 1 K) : ((hermBlk X).map (bar 1))ᵀ = hermBlk X := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, hermBlk]
  exact herm_apply X (Fin.castLE (by decide) i) (Fin.castLE (by decide) j)

private theorem levi_mem {hK : Nat.card K = (2 ^ 1) ^ 2} (A : SL(2, K)) {X : HMod 1 K}
    (hX : X ∈ commOnR ⊤ (LW hK) ⊓ blkW 1 K) :
    rho hK (embW A) X ∈ commOnR ⊤ (LW hK) ⊓ blkW 1 K ∧
      hermBlk (rho hK (embW A) X) =
        (A : Matrix (Fin 2) (Fin 2) K) * hermBlk X *
          ((A : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ := by
  obtain ⟨hXU, hXB⟩ := Subgroup.mem_inf.1 hX
  have hemb : embW A ∈ stabW K := ⟨(embW_mem_perfW A).1, (embW_mem_perfW A).2.1⟩
  obtain ⟨hYB, hYblk⟩ := hermBlk_rho le_rfl hK hemb hXB
  rw [blkMat_embW] at hYblk
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hU : rho hK (embW A) X * X⁻¹ ∈ commOnR ⊤ (LW hK) :=
    mem_commOnR_of (rho hK (embW A)) (rho_embW_mem_LW h4 A) X
  refine ⟨Subgroup.mem_inf.2 ⟨?_, hYB⟩, hYblk⟩
  have := mul_mem hU hXU
  rwa [inv_mul_cancel_right] at this

private theorem hermBlkSub_nonzero (hK : Nat.card K = (2 ^ 1) ^ 2) :
    ∃ B ∈ hermBlkSub (commOnR ⊤ (LW hK) ⊓ blkW 1 K), B ≠ 0 := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : HMod 1 K, mat X₀ = !![1, 0, 0; 0, 0, 0; 0, 0, 0] :=
    ⟨mkH (!![1, 0, 0; 0, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) K) (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjM]), rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : SL(2, K), (A₁ : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 1, 1] :=
    ⟨⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩, rfl⟩
  have hX₀B : X₀ ∈ blkW 1 K := by
    rw [mem_blkW, hX₀]
    simp
  have hemb : embW A₁ ∈ stabW K := ⟨(embW_mem_perfW A₁).1, (embW_mem_perfW A₁).2.1⟩
  obtain ⟨hYB, -⟩ := hermBlk_rho le_rfl hK hemb hX₀B
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have hZ : rho hK (embW A₁) X₀ * X₀⁻¹ ∈ commOnR ⊤ (LW hK) ⊓ blkW 1 K :=
    Subgroup.mem_inf.2 ⟨mem_commOnR_of (rho hK (embW A₁)) (rho_embW_mem_LW h4 A₁) X₀,
      mul_mem hYB (inv_mem hX₀B)⟩
  have hY01 : mat (rho hK (embW A₁) X₀) 0 1 = 1 := by
    rw [mat_rho, hX₀]
    simp [tw, conjM, Matrix.mul_apply, Fin.sum_univ_three, embW, hA₁]
  have hZ01 : mat (rho hK (embW A₁) X₀ * X₀⁻¹) 0 1 = 1 := by
    simp [mat_mul, mat_inv, hY01, hX₀]
  refine ⟨hermBlk (rho hK (embW A₁) X₀ * X₀⁻¹), mem_hermBlkSub.2 ⟨_, hZ, rfl⟩, ?_⟩
  intro h
  have h01 : mat (rho hK (embW A₁) X₀ * X₀⁻¹) 0 1 = 0 := congrFun (congrFun h 0) 1
  rw [hZ01] at h01
  exact one_ne_zero h01

theorem blkW_le_commOnR (hK : Nat.card K = (2 ^ 1) ^ 2) : blkW 1 K ≤ commOnR ⊤ (LW hK) := by
  intro Y hY
  have hall := irr_herm (S := hermBlkSub (commOnR ⊤ (LW hK) ⊓ blkW 1 K)) hK
    (fun B hB => by
      obtain ⟨X, -, rfl⟩ := mem_hermBlkSub.1 hB
      exact hermBlk_herm X)
    (fun A B hB => by
      obtain ⟨X, hX, rfl⟩ := mem_hermBlkSub.1 hB
      exact mem_hermBlkSub.2 ⟨rho hK (embW A) X, (levi_mem A hX).1, (levi_mem A hX).2⟩)
    (hermBlkSub_nonzero hK)
  obtain ⟨X, hX, hXY⟩ := mem_hermBlkSub.1 (hall (hermBlk Y) (hermBlk_herm Y))
  have hXY' : X = Y := eq_of_hermBlk_eq (Subgroup.mem_inf.1 hX).2 hY hXY
  rw [← hXY']
  exact (Subgroup.mem_inf.1 hX).1

end CFSG.Quasithin.RonanH46

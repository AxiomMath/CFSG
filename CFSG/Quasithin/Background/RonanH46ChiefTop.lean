module

public import CFSG.Quasithin.Background.RonanH46ZLev
public import CFSG.Quasithin.Background.RonanH46Irr

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem chief_hermBlkZ_one {n : ℕ} : hermBlkZ (1 : HMod n K) = 0 := by
  ext i j
  simp [hermBlkZ, mat_one]

private theorem chief_hermBlkZ_mul {n : ℕ} (X Y : HMod n K) :
    hermBlkZ (X * Y) = hermBlkZ X + hermBlkZ Y := by
  ext i j
  simp [hermBlkZ, mat_mul]

private theorem chief_hermBlkZ_inv {n : ℕ} (X : HMod n K) : hermBlkZ X⁻¹ = -hermBlkZ X := by
  ext i j
  simp [hermBlkZ, mat_inv]

private theorem chief_hermBlkZ_herm {n : ℕ} (X : HMod n K) :
    ((hermBlkZ X).map (bar n))ᵀ = hermBlkZ X := by
  ext i j
  simp [hermBlkZ, herm_apply]

theorem chief_V2z_top (hK : Nat.card K = (2 ^ 1) ^ 2) :
    IsChiefFactorUnderR (actsOnModuleR (LZ hK)) (V2z 1 K) ⊤ := by
  have h4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  unfold IsChiefFactorUnderR IsActsInvR
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    have hA : (conjM 1 (1 : Matrix (Fin 3) (Fin 3) K))ᵀ = 1 := by
      rw [conjM_one, transpose_one]
    refine lt_of_le_of_ne le_top fun h => ?_
    have hmem : mkH (1 : Matrix (Fin 3) (Fin 3) K) hA ∈ V2z 1 K := by
      rw [h]
      exact Subgroup.mem_top _
    simp [mem_V2z, mat_mkH] at hmem
  ·
    intro f hf u hu
    obtain ⟨y, hy, rfl⟩ := hf
    exact LZ_mem_V2z hK hy hu
  ·
    intro f _ u _
    exact Subgroup.mem_top _
  · intro W hVW _ hW
    obtain ⟨S, hSmem⟩ : ∃ S : AddSubgroup (Matrix (Fin 2) (Fin 2) K),
        ∀ B, B ∈ S ↔ ∃ X ∈ W, hermBlkZ X = B :=
      ⟨{ carrier := {B | ∃ X ∈ W, hermBlkZ X = B}
         zero_mem' := ⟨1, W.one_mem, chief_hermBlkZ_one⟩
         add_mem' := by
           rintro _ _ ⟨X, hX, rfl⟩ ⟨Y, hY, rfl⟩
           exact ⟨X * Y, W.mul_mem hX hY, chief_hermBlkZ_mul X Y⟩
         neg_mem' := by
           rintro _ ⟨X, hX, rfl⟩
           exact ⟨X⁻¹, W.inv_mem hX, chief_hermBlkZ_inv X⟩ }, fun _ => Iff.rfl⟩
    have hS : ∀ (A : SL(2, K)) (B : Matrix (Fin 2) (Fin 2) K), B ∈ S →
        (A : Matrix (Fin 2) (Fin 2) K) * B * ((A : Matrix (Fin 2) (Fin 2) K).map (bar 1))ᵀ ∈ S := by
      intro A B hB
      obtain ⟨X, hX, rfl⟩ := (hSmem _).1 hB
      obtain ⟨y, hy, hyX⟩ := exists_LZ_hermBlkZ hK h4 A
      exact (hSmem _).2 ⟨y X, hW (fun v => y v) ⟨y, hy, rfl⟩ X hX, hyX X⟩
    have hherm : ∀ B ∈ S, (B.map (bar 1))ᵀ = B := by
      intro B hB
      obtain ⟨X, -, rfl⟩ := (hSmem _).1 hB
      exact chief_hermBlkZ_herm X
    by_cases hne : ∃ B ∈ S, B ≠ 0
    ·
      refine Or.inr (eq_top_iff.2 fun Y _ => ?_)
      obtain ⟨X, hX, hXY⟩ : ∃ X ∈ W, hermBlkZ X = hermBlkZ Y :=
        (hSmem _).1 (irr_herm hK hherm hS hne _ (chief_hermBlkZ_herm Y))
      have hmem : Y * X⁻¹ ∈ V2z 1 K := by
        rw [mem_V2z_iff_hermBlkZ, chief_hermBlkZ_mul, chief_hermBlkZ_inv, hXY]
        simp
      simpa using W.mul_mem (hVW hmem) hX
    ·
      push_neg at hne
      refine Or.inl (le_antisymm (fun X hX => ?_) hVW)
      rw [mem_V2z_iff_hermBlkZ]
      exact hne (hermBlkZ X) ((hSmem _).2 ⟨X, hX, rfl⟩)

end CFSG.Quasithin.RonanH46

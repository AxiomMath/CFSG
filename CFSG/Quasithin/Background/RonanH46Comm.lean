module

public import CFSG.Quasithin.Background.RonanH46ComCol
public import CFSG.Quasithin.Background.RonanH46ComBlk
public import CFSG.Quasithin.Background.RonanH45C
public import CFSG.Quasithin.Background.RonanH46Fml

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44 CFSG.Quasithin.RonanH45
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem commOnR_le_Hhyp (hK : Nat.card K = (2 ^ n) ^ 2) : commOnR ⊤ (LW hK) ≤ Hhyp n K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨a, ha, w, -, rfl⟩
  obtain ⟨g₀, hg₀, rfl⟩ := mem_LW ha
  rw [SetLike.mem_coe, mem_Hhyp, mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply,
    rhoW_entry22 hK hg₀, add_neg_cancel]

theorem Hhyp_le_commOnR (hK : Nat.card K = (2 ^ 1) ^ 2) : Hhyp 1 K ≤ commOnR ⊤ (LW hK) := by
  intro X hX
  rw [mem_Hhyp] at hX
  have hY : X * (colH hK ![mat X 0 2, mat X 1 2])⁻¹ ∈ blkW 1 K := by
    rw [mem_blkW]
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [mat_mul, mat_inv, mat_colH, colMat, hX]
  have h := mul_mem (blkW_le_commOnR hK hY) (col_mem_commOnR hK ![mat X 0 2, mat X 1 2])
  rwa [inv_mul_cancel_right] at h

theorem V2z_le_commOnR (hK : Nat.card K = (2 ^ 1) ^ 2) : V2z 1 K ≤ commOnR ⊤ (LW hK) := by
  intro X hX
  exact Hhyp_le_commOnR hK (mem_Hhyp.2 (mem_V2z.1 hX).2.2)

end CFSG.Quasithin.RonanH46

module

public import CFSG.Quasithin.Background.RonanH46Irr
public import CFSG.Quasithin.Background.RonanH46Defs

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def colMat (c : Fin 2 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, c 0; 0, 0, c 1; bar 1 (c 0), bar 1 (c 1), 0]

theorem colMat_herm (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Fin 2 → K) :
    (conjM 1 (colMat c))ᵀ = colMat c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [colMat, conjM, bar_bar hK]

@[expose] noncomputable def colH (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Fin 2 → K) : HMod 1 K :=
  mkH (colMat c) (colMat_herm hK c)

theorem mat_colH (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Fin 2 → K) :
    mat (colH hK c) = colMat c :=
  rfl

private theorem colH_add (hK : Nat.card K = (2 ^ 1) ^ 2) (c c' : Fin 2 → K) :
    colH hK (c + c') = colH hK c * colH hK c' := by
  refine mat_injective ?_
  rw [mat_mul, mat_colH, mat_colH, mat_colH]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [colMat, map_add]

private theorem colH_zero (hK : Nat.card K = (2 ^ 1) ^ 2) : colH hK 0 = 1 := by
  refine mat_injective ?_
  rw [mat_colH, mat_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [colMat]

private theorem colH_neg (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Fin 2 → K) :
    colH hK (-c) = (colH hK c)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← colH_add, neg_add_cancel, colH_zero]

private theorem tw_embW_colMat (A : SL(2, K)) (c : Fin 2 → K) :
    tw 1 (embW A : Matrix (Fin 3) (Fin 3) K) (colMat c) =
      colMat ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tw, colMat, embW, conjM, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, map_add, map_mul] <;> ring

private theorem rho_embW_colH (hK : Nat.card K = (2 ^ 1) ^ 2) (A : SL(2, K)) (c : Fin 2 → K) :
    rho hK (embW A) (colH hK c) = colH hK ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ c) := by
  refine mat_injective ?_
  rw [mat_rho, mat_colH, mat_colH]
  exact tw_embW_colMat A c

theorem col_mem_commOnR (hK : Nat.card K = (2 ^ 1) ^ 2) (c : Fin 2 → K) :
    colH hK c ∈ commOnR ⊤ (LW hK) := by
  have h4 : 4 ≤ Nat.card K := by rw [hK] <;> norm_num
  let S : AddSubgroup (Fin 2 → K) :=
    { carrier := {x | colH hK x ∈ commOnR ⊤ (LW hK)}
      add_mem' := by
        intro a b ha hb
        change colH hK a ∈ commOnR ⊤ (LW hK) at ha
        change colH hK b ∈ commOnR ⊤ (LW hK) at hb
        change colH hK (a + b) ∈ commOnR ⊤ (LW hK)
        rw [colH_add hK]
        exact mul_mem ha hb
      zero_mem' := by
        change colH hK 0 ∈ commOnR ⊤ (LW hK)
        rw [colH_zero hK]
        exact one_mem _
      neg_mem' := by
        intro a ha
        change colH hK a ∈ commOnR ⊤ (LW hK) at ha
        change colH hK (-a) ∈ commOnR ⊤ (LW hK)
        rw [colH_neg hK]
        exact inv_mem ha }
  have hmemS : ∀ x : Fin 2 → K, x ∈ S ↔ colH hK x ∈ commOnR ⊤ (LW hK) :=
    fun x => Iff.rfl
  have hinv : ∀ (A : SL(2, K)) (v : Fin 2 → K), v ∈ S →
      (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ S := by
    intro A v hv
    have hv' : colH hK v ∈ commOnR ⊤ (LW hK) := (hmemS v).1 hv
    refine (hmemS _).2 ?_
    rw [← rho_embW_colH hK A v]
    have hgen : rho hK (embW A) (colH hK v) * (colH hK v)⁻¹ ∈ commOnR ⊤ (LW hK) := by
      unfold commOnR
      apply Subgroup.subset_closure
      exact ⟨rho hK (embW A), rho_embW_mem_LW (hK := hK) h4 A, colH hK v, Subgroup.mem_top _, rfl⟩
    have h := mul_mem hgen hv'
    rwa [inv_mul_cancel_right] at h
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : SL(2, K), (A₀ : Matrix (Fin 2) (Fin 2) K) = !![1, 1; 0, 1] :=
    ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩, rfl⟩
  have hv01 : (A₀ : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, 1] = ![1, 0] + ![0, 1] := by
    rw [hA₀]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hsum : rho hK (embW A₀) (colH hK ![0, 1]) = colH hK ![1, 0] * colH hK ![0, 1] := by
    rw [rho_embW_colH, hv01, colH_add]
  have hgen0 : rho hK (embW A₀) (colH hK ![0, 1]) * (colH hK ![0, 1])⁻¹ ∈
      commOnR ⊤ (LW hK) := by
    unfold commOnR
    apply Subgroup.subset_closure
    exact ⟨rho hK (embW A₀), rho_embW_mem_LW (hK := hK) h4 A₀, colH hK ![0, 1],
      Subgroup.mem_top _, rfl⟩
  have h10 : colH hK ![1, 0] ∈ commOnR ⊤ (LW hK) := by
    have h := hgen0
    rw [hsum, mul_inv_cancel_right] at h
    exact h
  have hmem10 : (![1, 0] : Fin 2 → K) ∈ S := (hmemS _).2 h10
  have hne10 : (![1, 0] : Fin 2 → K) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  rcases irr_natural (S := S) hinv with hbot | htop
  · rw [hbot] at hmem10
    exact absurd (AddSubgroup.mem_bot.1 hmem10) hne10
  · have hc : c ∈ S := by
      rw [htop]
      exact AddSubgroup.mem_top c
    exact (hmemS c).1 hc

end CFSG.Quasithin.RonanH46

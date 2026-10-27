module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57ModelBasic
public import CFSG.Quasithin.Background.JonesParshallSL3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

namespace C10P01

open Matrix CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Bridge.Alt57Model
open scoped commutatorElement

theorem sq_eq_one_of_pow_four_SL2 {F : Type} [Field F] [CharP F 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (h : g ^ 4 = 1) : g ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set M : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hM
  have hdet : M.det = 1 := g.2
  set t : F := M 0 0 + M 1 1 with ht
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hdet
  have hP : M ^ 2 = t • M + 1 := by
    ext i j
    revert i j
    simp only [Fin.forall_fin_two, sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide :
        (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), ht]
    refine ⟨⟨by linear_combination -hd - h2, by ring⟩, by ring, by linear_combination -hd - h2⟩
  have h4 : M ^ 4 = 1 := by
    have := congrArg
      (fun x : Matrix.SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) h
    simpa using this
  have hP2 : M ^ 4 = t ^ 2 • M ^ 2 + 1 := by
    have e : M ^ 4 = (t • M + 1) ^ 2 := by rw [← hP, ← pow_mul]
    rw [e, add_pow_char_of_commute (p := 2) (Commute.one_right _), smul_pow, one_pow]
  have hz : t ^ 2 • M ^ 2 = 0 := by
    have h1 : t ^ 2 • M ^ 2 + 1 = 0 + 1 := by rw [← hP2, h4, zero_add]
    exact add_right_cancel h1
  have ht0 : t = 0 := by
    have := congrArg Matrix.det hz
    rw [Matrix.det_smul, Matrix.det_pow, hdet, one_pow, mul_one, Matrix.det_zero,
      Fintype.card_fin] at this
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (pow_eq_zero_iff (by norm_num) |>.mp this)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hM, hP, ht0, zero_smul, zero_add]
  rfl

variable {K : Type} [Field K]

@[expose] def jMat3 (K : Type) [Field K] : SL3 K :=
  ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def pMat3 (K : Type) [Field K] : SL3 K :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [det_fin_three]⟩

theorem coe_jMat3_sq [CharP K 2] :
    ((jMat3 K ^ 2 : SL3 K) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 1; 0, 1, 0; 0, 0, 1] := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  rw [Matrix.SpecialLinearGroup.coe_pow, sq]
  change !![(1 : K), 1, 0; 0, 1, 1; 0, 0, 1] * !![(1 : K), 1, 0; 0, 1, 1; 0, 0, 1] = _
  rw [Matrix.mul_fin_three]
  simp [h2]

theorem jMat3_pow_four [CharP K 2] : jMat3 K ^ 4 = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  apply Subtype.ext
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Matrix.SpecialLinearGroup.coe_pow, coe_jMat3_sq, sq,
    Matrix.mul_fin_three, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_three]
  simp [h2]

theorem pMat3_pow_three : pMat3 K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  change !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] ^ 3 = 1
  rw [pow_three, Matrix.mul_fin_three, Matrix.mul_fin_three, Matrix.one_fin_three]
  simp

theorem jMat3_sq_not_mem_center [CharP K 2] : jMat3 K ^ 2 ∉ Subgroup.center (SL3 K) := by
  intro hmem
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
  have h02 := congrFun (congrFun hr 0) 2
  rw [coe_jMat3_sq] at h02
  simp at h02

theorem pMat3_not_mem_center : pMat3 K ∉ Subgroup.center (SL3 K) := by
  intro hmem
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hmem
  have h02 := congrFun (congrFun hr 0) 2
  change Matrix.scalar (Fin 3) r 0 2 = !![(0 : K), 0, 1; 1, 0, 0; 0, 1, 0] 0 2 at h02
  simp at h02

end C10P01

end CFSG.Quasithin.Vol2.Ch10.SecA

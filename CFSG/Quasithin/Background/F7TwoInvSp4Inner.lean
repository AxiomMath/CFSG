module

public import CFSG.Quasithin.Background.F7TwoInvSp4Lagr
public import CFSG.Quasithin.Background.F7TwoInvSp4Crit

public section

namespace CFSG.Quasithin.F7Two

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

variable {K : Type} [Field K] [CharP K 2]

theorem invAutGen_conj_ut {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C)
    (hW : ∀ n : ℕ, (upperUnipotentSp 2 K hC * lowerSp hC) ^ 2 ^ n ≠ 1) :
    InvAutGen (StatedSp 2 K) (MulAut.conj (upperUnipotentSp 2 K hC)) := by
  have hinv : (upperUnipotentSp 2 K hC)⁻¹ = upperUnipotentSp 2 K hC :=
    inv_eq_of_mul_eq_one_right (ut_mul_self hC)
  refine invAutGen_of_mem_invXiAut (x := sp4J) ?_ ?_
  · rw [mem_invXiAut_iff]
    intro n
    have h : (MulAut.conj (upperUnipotentSp 2 K hC)) sp4J * sp4J⁻¹ =
        upperUnipotentSp 2 K hC * lowerSp hC := by
      rw [MulAut.conj_apply, hinv, inv_sp4J, lowerSp]
      simp only [mul_assoc]
    rw [h]
    exact hW n
  · intro H hH hJ
    refine eq_top_of_tau_mem_of_sp4J_mem (fun D hD => hH ?_) hJ
    rw [mem_fixSubgroup_iff, MulAut.conj_apply, hinv]
    calc upperUnipotentSp 2 K hC * upperUnipotentSp 2 K hD * upperUnipotentSp 2 K hC
        = upperUnipotentSp 2 K hD * upperUnipotentSp 2 K hC * upperUnipotentSp 2 K hC := by
          rw [ut_comm hC hD]
      _ = upperUnipotentSp 2 K hD := by rw [mul_assoc, ut_mul_self hC, mul_one]

theorem coe_ut_mul_lowerSp {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (((upperUnipotentSp 2 K hC * lowerSp hC : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (1 + C * C) C C 1 := by
  rw [Subgroup.coe_mul, Units.val_mul, coe_upperUnipotentSp, coe_lowerSp, fromBlocks_multiply]
  simp

theorem invAutGen_conj_ut_of_isUnit {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C)
    (hu : IsUnit C.det) : InvAutGen (StatedSp 2 K) (MulAut.conj (upperUnipotentSp 2 K hC)) := by
  refine invAutGen_conj_ut hC fun n => pow_two_pow_ne_one_of_isUnit_sub_one ?_ n
  rw [coe_ut_mul_lowerSp]
  have hCCi : C * C⁻¹ = 1 := Matrix.mul_nonsing_inv C hu
  have hN : (fromBlocks (1 + C * C) C C 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) - 1 =
      fromBlocks (C * C) C C 0 := by
    rw [sub_eq_iff_eq_add, ← fromBlocks_one, fromBlocks_add]
    simp [add_comm]
  have hX : (fromBlocks (C * C) C C 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      fromBlocks 0 C⁻¹ C⁻¹ (-1) = 1 := by
    have e1 : C * C * C⁻¹ = C := by rw [Matrix.mul_assoc, hCCi, Matrix.mul_one]
    rw [fromBlocks_multiply]
    simp [e1, hCCi, fromBlocks_one]
  rw [hN]
  exact (Units.mk _ _ hX (mul_eq_one_comm.mp hX)).isUnit

theorem fromBlocks_pow_three (E : Matrix (Fin 2) (Fin 2) K) (hE : E * E = E) :
    (fromBlocks (1 + E) E E 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 3 = 1 := by
  have hE2 : E + E = 0 := CharTwo.add_self_eq_zero E
  have hFE : (1 + E) * E = 0 := by rw [add_mul, one_mul, hE, hE2]
  have hEF : E * (1 + E) = 0 := by rw [mul_add, mul_one, hE, hE2]
  have hFF : (1 + E) * (1 + E) = 1 + E := by
    calc (1 + E) * (1 + E) = 1 + (E + E) + E * E := by noncomm_ring
      _ = 1 + E := by rw [hE2, hE, add_zero]
  have h1 : 1 + E + E = 1 := by rw [add_assoc, hE2, add_zero]
  have h3 : E + (1 + E) = 1 := by rw [← add_assoc, add_comm E 1, h1]
  have hM2 : (fromBlocks (1 + E) E E 1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ^ 2 =
      fromBlocks 1 E E (1 + E) := by
    rw [sq, fromBlocks_multiply]
    simp only [hFF, hFE, hEF, hE, Matrix.mul_one, Matrix.one_mul, zero_add, h1]
    rw [add_comm E 1]
  rw [pow_succ, hM2, fromBlocks_multiply]
  simp only [hFE, hEF, hE, Matrix.mul_one, Matrix.one_mul, add_zero, hE2, h1, h3, fromBlocks_one]

theorem invAutGen_conj_ut_single (hE : (single 0 0 1 : Matrix (Fin 2) (Fin 2) K)ᵀ = single 0 0 1) :
    InvAutGen (StatedSp 2 K) (MulAut.conj (upperUnipotentSp 2 K hE)) := by
  have hEE : (single 0 0 1 : Matrix (Fin 2) (Fin 2) K) * single 0 0 1 = single 0 0 1 := by
    rw [single_mul_single_same, mul_one]
  refine invAutGen_conj_ut hE fun n => pow_two_pow_ne_one_of_pow_three ?_ ?_ n
  · refine statedSp_ext ?_
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_ut_mul_lowerSp, hEE,
      fromBlocks_pow_three _ hEE, Subgroup.coe_one, Units.val_one]
  · intro h
    have h1 := congrArg (fun z : StatedSp 2 K => ((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
    simp only [coe_ut_mul_lowerSp, hEE, Subgroup.coe_one, Units.val_one] at h1
    rw [← fromBlocks_one] at h1
    have h2 := congrFun₂ (fromBlocks_inj.mp h1).2.1 0 0
    simp at h2

theorem invAutGen_conj_of_sp4_involution [Finite K] {g : StatedSp 2 K} (hg2 : g * g = 1)
    (hg1 : g ≠ 1) : InvAutGen (StatedSp 2 K) (MulAut.conj g) := by
  obtain ⟨h, C, hC, hC0, hhg⟩ := exists_conj_eq_ut hg2 hg1
  rw [InvAutGen.conj_iff (MulAut.conj h)]
  have hconj : MulAut.conj h * MulAut.conj g * (MulAut.conj h)⁻¹ =
      MulAut.conj (upperUnipotentSp 2 K hC) := by
    rw [← hhg, map_mul, map_mul, map_inv]
  rw [hconj]
  rcases isUnit_det_or_exists_conj_eq_single hC hC0 with hu | ⟨A, hA⟩
  · exact invAutGen_conj_ut_of_isUnit hC hu
  · have hE : (single 0 0 1 : Matrix (Fin 2) (Fin 2) K)ᵀ = single 0 0 1 := by
      rw [transpose_single]
    rw [InvAutGen.conj_iff (MulAut.conj (leviSp A))]
    have hconj2 : MulAut.conj (leviSp A) * MulAut.conj (upperUnipotentSp 2 K hC) *
        (MulAut.conj (leviSp A))⁻¹ = MulAut.conj (upperUnipotentSp 2 K hE) := by
      rw [← map_inv, ← map_mul, ← map_mul, leviSp_mul_ut_mul_inv]
      exact congrArg _ (ut_congr hA _ _)
    rw [hconj2]
    exact invAutGen_conj_ut_single hE

end CFSG.Quasithin.F7Two

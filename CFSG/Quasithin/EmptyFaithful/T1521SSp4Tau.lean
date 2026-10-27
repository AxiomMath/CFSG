module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveTauGrp

public section

namespace CFSG.Quasithin.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.QuasithinUnique.Lin2.Five

variable {F : Type} [Field F]

theorem tauSp_tauS [CharP F 2] (b c d : F) :
    tauSp (tauS b c d) = lam d * tauS (c ^ 2) b 0 := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp, Subgroup.coe_mul, Units.val_mul, coe_lam, coe_tauS, coe_tauS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tauMat, tauPair, sym2, unitri, Matrix.fromBlocks, Matrix.one_apply, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, CharTwo.neg_eq, CharTwo.sub_eq_add]
  all_goals ring

theorem tauSp_lam [CharP F 2] (a : F) : tauSp (lam a) = tauS 0 0 (a ^ 2) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp, coe_lam, coe_tauS]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tauMat, tauPair, sym2, unitri, Matrix.fromBlocks, CharTwo.neg_eq, CharTwo.sub_eq_add]
  all_goals ring

theorem tauSp_tauS_zero [CharP F 2] (b c : F) : tauSp (tauS b c 0) = tauS (c ^ 2) b 0 := by
  rw [tauSp_tauS, lam_zero, one_mul]

theorem tauSp_mem_unipotent [CharP F 2] {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) :
    tauSp g ∈ unipotent 2 F := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.mp hg
  rw [map_mul, tau_eq_tauS, tauSp_tauS, tauSp_lam]
  exact mul_mem (mul_mem (lam_mem_unipotent _) (tauS_mem_unipotent _ _ _))
    (tauS_mem_unipotent _ _ _)

theorem fieldSp_tauS (σ : F ≃+* F) (b c d : F) :
    SymplecticHigher.fieldSp 2 F σ (tauS b c d) = tauS (σ b) (σ c) (σ d) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [SymplecticHigher.coe_fieldSp, coe_tauS, coe_tauS]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [sym2, Matrix.fromBlocks]

theorem fieldSp_lam [CharP F 2] (σ : F ≃+* F) (a : F) :
    SymplecticHigher.fieldSp 2 F σ (lam a) = lam (σ a) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [SymplecticHigher.coe_fieldSp, coe_lam, coe_lam]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [unitri, Matrix.fromBlocks, CharTwo.neg_eq]

theorem fieldSp_mem_unipotent [CharP F 2] (σ : F ≃+* F) {g : StatedSp 2 F}
    (hg : g ∈ unipotent 2 F) : SymplecticHigher.fieldSp 2 F σ g ∈ unipotent 2 F := by
  obtain ⟨C, hC, a, rfl⟩ := mem_unipotent_iff.mp hg
  rw [map_mul, tau_eq_tauS, fieldSp_tauS, fieldSp_lam]
  exact mul_mem (tauS_mem_unipotent _ _ _) (lam_mem_unipotent _)

theorem tauS_injective {b c d b' c' d' : F} (h : tauS b c d = tauS b' c' d') :
    b = b' ∧ c = c' ∧ d = d' := by
  have h' := congrArg (fun g : StatedSp 2 F => ((g : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  simp only [coe_tauS] at h'
  have h0 := congrFun₂ (fromBlocks_inj.1 h').2.1 0 0
  have h1 := congrFun₂ (fromBlocks_inj.1 h').2.1 0 1
  have h2 := congrFun₂ (fromBlocks_inj.1 h').2.1 1 1
  simp [sym2] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem tauS_mul_lam_injective {b c d a b' c' d' a' : F}
    (h : tauS b c d * lam a = tauS b' c' d' * lam a') :
    b = b' ∧ c = c' ∧ d = d' ∧ a = a' := by
  have h' := congrArg (fun g : StatedSp 2 F => ((g : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) h
  simp only [Subgroup.coe_mul, Units.val_mul, coe_tauS, coe_lam] at h'
  have e01 := congrFun₂ h' (Sum.inl 0) (Sum.inl 1)
  have e02 := congrFun₂ h' (Sum.inl 0) (Sum.inr 0)
  have e03 := congrFun₂ h' (Sum.inl 0) (Sum.inr 1)
  have e13 := congrFun₂ h' (Sum.inl 1) (Sum.inr 1)
  simp [sym2, unitri, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type,
    Fin.sum_univ_two] at e01 e02 e03 e13
  subst e01 e03 e13
  exact ⟨by linear_combination e02, rfl, rfl, rfl⟩

end CFSG.Quasithin.Sp4

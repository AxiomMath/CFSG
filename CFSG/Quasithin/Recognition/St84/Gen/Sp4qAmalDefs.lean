module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks


public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type*} [Group G]

structure Sp4qLocalData (L1 L2 S : Subgroup G) (f : ℕ) : Prop where
  card_S : Nat.card S = 2 ^ (4 * f)
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ (3 * f)
  elem_left : IsElemAbelian 2 (pCoreOf 2 L1)
  lin_left : IsLin2Type L1 f
  indec_left : ⁅pCoreOf 2 L1, L1⁆ = pCoreOf 2 L1
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ (3 * f)
  elem_right : IsElemAbelian 2 (pCoreOf 2 L2)
  lin_right : IsLin2Type L2 f
  indec_right : ⁅pCoreOf 2 L2, L2⁆ = pCoreOf 2 L2
  card_inf : Nat.card ↥(pCoreOf 2 L1 ⊓ pCoreOf 2 L2) = 2 ^ (2 * f)

theorem Sp4qLocalData.symm {L1 L2 S : Subgroup G} {f : ℕ} (h : Sp4qLocalData L1 L2 S f) :
    Sp4qLocalData L2 L1 S f :=
  ⟨h.card_S, h.card_right, h.elem_right, h.lin_right, h.indec_right, h.card_left, h.elem_left,
    h.lin_left, h.indec_left, by rw [inf_comm]; exact h.card_inf⟩

section Matrices

variable {F : Type*} [Field F]

@[expose] def sp4RadMat (M : SL(2, F)) : Matrix (Fin 3) (Fin 3) F :=
  !![1, M 1 0 * M 0 0, M 1 1 * M 0 1;
    0, M 0 0 ^ 2, M 0 1 ^ 2;
    0, M 1 0 ^ 2, M 1 1 ^ 2]

theorem sp4RadMat_one : sp4RadMat (1 : SL(2, F)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sp4RadMat, Matrix.one_apply]

theorem sp4RadMat_mul [CharP F 2] (M N : SL(2, F)) :
    sp4RadMat (M * N) = sp4RadMat M * sp4RadMat N := by
  have hM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have h := M.2
    rwa [Matrix.det_fin_two] at h
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sp4RadMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.SpecialLinearGroup.coe_mul,
      Fin.sum_univ_two]
  all_goals first
    | ring1
    | linear_combination (N 0 0 * N 1 0) * hM + (M 1 0 * M 0 1 * N 0 0 * N 1 0) * h2
    | linear_combination (N 0 1 * N 1 1) * hM + (M 1 0 * M 0 1 * N 0 1 * N 1 1) * h2
    | linear_combination (M 0 0 * N 0 0 * M 0 1 * N 1 0) * h2
    | linear_combination (M 0 0 * N 0 1 * M 0 1 * N 1 1) * h2
    | linear_combination (M 1 0 * N 0 0 * M 1 1 * N 1 0) * h2
    | linear_combination (M 1 0 * N 0 1 * M 1 1 * N 1 1) * h2

theorem sp4RadMat_mulVec (M : SL(2, F)) (v : Fin 3 → F) :
    (sp4RadMat M).mulVec v = ![v 0 + M 1 0 * M 0 0 * v 1 + M 1 1 * M 0 1 * v 2,
      M 0 0 ^ 2 * v 1 + M 0 1 ^ 2 * v 2, M 1 0 ^ 2 * v 1 + M 1 1 ^ 2 * v 2] := by
  ext i
  fin_cases i <;> simp [sp4RadMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

@[expose] noncomputable def sp4RadHom (F : Type*) [Field F] [CharP F 2] :
    SL(2, F) →* GL (Fin 3) F where
  toFun M := ⟨sp4RadMat M, sp4RadMat M⁻¹, by rw [← sp4RadMat_mul, mul_inv_cancel, sp4RadMat_one],
    by rw [← sp4RadMat_mul, inv_mul_cancel, sp4RadMat_one]⟩
  map_one' := Units.ext sp4RadMat_one
  map_mul' M N := Units.ext (sp4RadMat_mul M N)

@[simp] theorem coe_sp4RadHom [CharP F 2] (M : SL(2, F)) :
    ((sp4RadHom F M : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = sp4RadMat M :=
  rfl

@[expose] noncomputable def sp4ScalarHom (F : Type*) [Field F] : Fˣ →* GL (Fin 3) F :=
  Units.map (Matrix.scalar (Fin 3) : F →+* Matrix (Fin 3) (Fin 3) F).toMonoidHom

@[simp] theorem coe_sp4ScalarHom (c : Fˣ) :
    ((sp4ScalarHom F c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (c : F) • 1 := by
  simp [sp4ScalarHom, Matrix.smul_one_eq_diagonal]

@[expose] noncomputable def sp4GammaHom (F : Type*) [Field F] [CharP F 2] :
    SL(2, F) × Fˣ →* GL (Fin 3) F :=
  MonoidHom.noncommCoprod (sp4RadHom F) (sp4ScalarHom F) fun M c => by
    refine Units.ext ?_
    simp only [Units.val_mul, coe_sp4RadHom, coe_sp4ScalarHom]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

@[expose] noncomputable def sp4Gamma (F : Type*) [Field F] [CharP F 2] : Subgroup (GL (Fin 3) F) :=
  (sp4GammaHom F).range

theorem mem_sp4Gamma_iff [CharP F 2] {A : GL (Fin 3) F} :
    A ∈ sp4Gamma F ↔
      ∃ (M : SL(2, F)) (c : Fˣ), (A : Matrix (Fin 3) (Fin 3) F) = (c : F) • sp4RadMat M := by
  constructor
  · rintro ⟨⟨M, c⟩, rfl⟩
    refine ⟨M, c, ?_⟩
    simp [sp4GammaHom, Matrix.mul_smul]
  · rintro ⟨M, c, hA⟩
    refine ⟨(M, c), Units.ext ?_⟩
    simp [sp4GammaHom, Matrix.mul_smul, hA]

end Matrices

end CFSG.Quasithin.F112R.St84

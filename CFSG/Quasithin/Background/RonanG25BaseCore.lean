module

public import CFSG.Quasithin.Background.RonanG25BaseDefs

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.Quasithin.SL3Model
open scoped MatrixGroups Matrix

section Core

variable {F : Type} [Field F]

theorem Pt_entries {g : SL(3, F)} (hg : g ∈ Pt (vE F 0)) :
    g.1 1 0 = 0 ∧ g.1 2 0 = 0 := mem_Pt_e0.1 hg

theorem ablk_mul {g h : SL(3, F)} (hg : g ∈ Pt (vE F 0)) :
    ablk (g * h) = ablk g * ablk h := by
  obtain ⟨h10, h20⟩ := Pt_entries hg
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ablk, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three, h10, h20]

theorem ablk_one : ablk (1 : SL(3, F)) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ablk]

noncomputable def ablkHom : ↥(Pt (vE F 0)) →* Matrix.GeneralLinearGroup (Fin 2) F where
  toFun g :=
    { val := ablk g.1
      inv := ablk g.1⁻¹
      val_inv := by rw [← ablk_mul g.2, mul_inv_cancel, ablk_one]
      inv_val := by rw [← ablk_mul (inv_mem g.2), inv_mul_cancel, ablk_one] }
  map_one' := Units.ext ablk_one
  map_mul' g h := Units.ext (ablk_mul g.2)

theorem ablkHom_coe (g : ↥(Pt (vE F 0))) :
    ((ablkHom g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ablk g.1 := by
  rfl

theorem ablk_blk (M : SL(2, F)) : ablk (CFSG.Quasithin.SL3Model.blk M) = M.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ablk, blk_coe]

noncomputable def glDual : Matrix.GeneralLinearGroup (Fin 2) F →* Matrix.GeneralLinearGroup (Fin 2) F where
  toFun g :=
    { val := ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ
      inv := ((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ
      val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
      inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one] }
  map_one' := Units.ext (by simp)
  map_mul' g h := Units.ext (by simp [Matrix.transpose_mul])

theorem glDual_coe (g : Matrix.GeneralLinearGroup (Fin 2) F) :
    ((glDual g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ := by
  rfl

theorem dual_entries {g : SL(3, F)} (hg : g ∈ Pt (vE F 0)) :
    ablk (dualHom F 3 g) = ((((ablkHom ⟨g, hg⟩)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F))ᵀ ∧
    (dualHom F 3 g).1 0 1 = 0 ∧ (dualHom F 3 g).1 0 2 = 0 ∧ (dualHom F 3 g).1 0 0 * g.1 0 0 = 1 := by
  have hinv : g⁻¹ ∈ Pt (vE F 0) := inv_mem hg
  have hent := Pt_entries hinv
  have hval : ((((ablkHom ⟨g, hg⟩)⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)) = ablk g⁻¹ := by
    rw [← map_inv ablkHom]
    exact ablkHom_coe ⟨g⁻¹, hinv⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hval]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ablk, dualHom_apply, slT_coe]
  · rw [dualHom_apply, slT_coe, Matrix.transpose_apply]
    exact hent.1
  · rw [dualHom_apply, slT_coe, Matrix.transpose_apply]
    exact hent.2
  · rw [dualHom_apply, slT_coe, Matrix.transpose_apply]
    have h1 : g⁻¹ * g = 1 := inv_mul_cancel g
    have h2 := congrArg (fun A : SL(3, F) => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_apply, Fin.sum_univ_three, (Pt_entries hg).1, (Pt_entries hg).2,
      Matrix.one_apply_eq, mul_zero, add_zero] at h2
    exact h2

variable [Finite F] [CharP F 2]

theorem exists_blk_transitive {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ M ∈ commutator SL(2, F), M.1.mulVec v = w := by
  rcases card_two_or_exists_sq_ne_one (F := F) with h2 | ⟨a, ha0, ha1⟩
  ·
    have key : ∀ u : Fin 2 → F, u ≠ 0 → ∃ N ∈ commutator SL(2, F), N • u = ![1, 0] := by
      intro u hu
      have hc : c3 F ∈ commutator SL(2, F) := CFSG.Quasithin.SL3Model.c3_mem_commutator
      have h11 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
      rcases eq_zero_or_one_of_card_two h2 (u 0) with h0 | h0 <;>
        rcases eq_zero_or_one_of_card_two h2 (u 1) with h1 | h1
      · exact (hu (funext fun i => by fin_cases i <;> simp [h0, h1])).elim
      · refine ⟨c3 F ^ 2, pow_mem hc 2, ?_⟩
        rw [pow_two, mul_smul, c3_smul, c3_smul]
        ext i
        fin_cases i <;> simp [h0, h1, h11]
      · refine ⟨1, one_mem _, ?_⟩
        rw [one_smul]
        funext i
        fin_cases i <;> simp [h0, h1]
      · refine ⟨c3 F, hc, ?_⟩
        rw [c3_smul]
        ext i
        fin_cases i <;> simp [h0, h1, h11]
    obtain ⟨Nv, hNv, hNv'⟩ := key v hv
    obtain ⟨Nw, hNw, hNw'⟩ := key w hw
    refine ⟨Nw⁻¹ * Nv, mul_mem (inv_mem hNw) hNv, ?_⟩
    show (Nw⁻¹ * Nv) • v = w
    rw [mul_smul, hNv', ← hNw', inv_smul_smul]
  ·
    have htop : commutator SL(2, F) = ⊤ := Matrix.SL2.commutator_eq_top ha0 ha1
    obtain ⟨A, hA⟩ := CFSG.Quasithin.SL2Model.exists_smul_eq v w hv hw
    exact ⟨A, by rw [htop]; exact Subgroup.mem_top A, hA⟩

theorem commutator_eq_top_of_two_lt (h : 2 < Nat.card F) : commutator SL(2, F) = ⊤ := by
  rcases card_two_or_exists_sq_ne_one (F := F) with h2 | ⟨a, ha0, ha1⟩
  · omega
  · exact Matrix.SL2.commutator_eq_top ha0 ha1

end Core

end CFSG.Quasithin.RonanG25

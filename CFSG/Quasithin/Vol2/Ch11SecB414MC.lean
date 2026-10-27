module

public import CFSG.Quasithin.Vol2.Ch11SecS12Q

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SteinbergBR.BlockPar
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

@[expose] def uMat (v : Fin 2 → F) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, v 0, v 1; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_uMat (v : Fin 2 → F) :
    (uMat v : Matrix (Fin 3) (Fin 3) F) = !![1, v 0, v 1; 0, 1, 0; 0, 0, 1] := rfl

theorem uMat_add (v w : Fin 2 → F) : uMat (v + w) = uMat v * uMat w := by
  apply Subtype.ext
  show (uMat (v + w) : Matrix (Fin 3) (Fin 3) F) = (uMat v : Matrix (Fin 3) (Fin 3) F) *
    (uMat w : Matrix (Fin 3) (Fin 3) F)
  rw [coe_uMat, coe_uMat, coe_uMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem uMat_zero : uMat (0 : Fin 2 → F) = 1 := by
  apply Subtype.ext
  show ((uMat (0 : Fin 2 → F) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1
  rw [coe_uMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem uMat_mem_radU (v : Fin 2 → F) : uMat v ∈ radU F (flagSpace 3 F 1) := by
  refine ⟨fun x => ?_, fun w hw => ?_⟩
  · rw [mem_flagSpace]
    intro j hj
    fin_cases j
    · simp at hj
    all_goals simp [coe_uMat, dotProduct, Fin.sum_univ_three]
  · rw [mem_flagSpace] at hw
    have h1 := hw 1 (by simp)
    have h2 := hw 2 (by simp)
    funext i
    fin_cases i <;> simp [coe_uMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

theorem eq_uMat_of_mem_radU {r : SpecialLinearGroup (Fin 3) F}
    (hr : r ∈ radU F (flagSpace 3 F 1)) :
    r = uMat ![(r : Matrix (Fin 3) (Fin 3) F) 0 1, (r : Matrix (Fin 3) (Fin 3) F) 0 2] := by
  apply Subtype.ext
  show (r : Matrix (Fin 3) (Fin 3) F) =
    ((uMat ![(r : Matrix (Fin 3) (Fin 3) F) 0 1, (r : Matrix (Fin 3) (Fin 3) F) 0 2] :
      SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  rw [coe_uMat]
  have hd := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.radU_diag hr
  have hrow : ∀ i : Fin 3, 1 ≤ (i : ℕ) → ∀ k,
      (r : Matrix (Fin 3) (Fin 3) F) i k = if i = k then 1 else 0 := fun i hi k =>
    CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.radU_row hr hi k
  ext i j
  fin_cases i
  · fin_cases j
    · simpa using hd 0
    · simp
    · simp
  all_goals fin_cases j <;> simp [hrow]

@[expose] noncomputable def iota0 : Multiplicative (Fin 2 → F) →* PGL3 F where
  toFun v := ProjGenLinGroup.mk (SpecialLinearGroup.toGL (uMat (Multiplicative.toAdd v)))
  map_one' := by rw [toAdd_one, uMat_zero, map_one, map_one]
  map_mul' v w := by rw [toAdd_mul, uMat_add, map_mul, map_mul]

theorem iota0_apply (v : Multiplicative (Fin 2 → F)) :
    iota0 v = ProjGenLinGroup.mk (SpecialLinearGroup.toGL (uMat (Multiplicative.toAdd v))) :=
  rfl

theorem iota0_injective : Function.Injective (iota0 (F := F)) := by
  intro v w h
  rw [iota0_apply, iota0_apply, ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨c, hc⟩ := h
  have hent : ∀ i j : Fin 3, ((uMat (Multiplicative.toAdd v) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) i j * (c : F) =
      ((uMat (Multiplicative.toAdd w) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) i j := fun i j => by
    have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) i j) hc
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply]
      using this
  have e11 := hent 1 1
  have e01 := hent 0 1
  have e02 := hent 0 2
  simp only [coe_uMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one,
    Fin.isValue, one_mul] at e11 e01 e02
  rw [e11, mul_one] at e01 e02
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · simpa using e01
  · simpa using e02

variable [Finite F] [CharP F 2]

theorem range_iota0 (hF : Nat.card F = 4) :
    (iota0 (F := F)).range = pCoreOf 2 (Ptheta F 0) := by
  ext y
  rw [CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.mem_pCoreOf_Ptheta hF]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨uMat (Multiplicative.toAdd v), uMat_mem_radU _, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    refine ⟨Multiplicative.ofAdd ![(r : Matrix (Fin 3) (Fin 3) F) 0 1,
      (r : Matrix (Fin 3) (Fin 3) F) 0 2], ?_⟩
    rw [iota0_apply, toAdd_ofAdd, ← eq_uMat_of_mem_radU hr]

@[expose] noncomputable def betaRef (hF : Nat.card F = 4) :
    ↥(pCoreOf 2 (Ptheta F 0)) ≃* Multiplicative (Fin 2 → F) :=
  ((MonoidHom.ofInjective (iota0_injective (F := F))).trans
    (MulEquiv.subgroupCongr (range_iota0 hF))).symm

theorem iota0_betaRef (hF : Nat.card F = 4) (u : ↥(pCoreOf 2 (Ptheta F 0))) :
    iota0 (betaRef hF u) = u := by
  have := congrArg (fun y : ↥(pCoreOf 2 (Ptheta F 0)) => (y : PGL3 F))
    ((betaRef hF).symm_apply_apply u)
  exact this

theorem betaRef_iota0 (hF : Nat.card F = 4) (v : Multiplicative (Fin 2 → F))
    (hv : iota0 v ∈ pCoreOf 2 (Ptheta F 0)) : betaRef hF ⟨iota0 v, hv⟩ = v := by
  apply iota0_injective
  rw [iota0_betaRef]

omit [Finite F] [CharP F 2] in
@[expose] def rhoMatG (g : GL (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i k => (g : Matrix (Fin 3) (Fin 3) F) 0 0 *
    ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) k.succ i.succ

omit [Finite F] [CharP F 2] in
theorem coe_mul_inv_GL (g : GL (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

omit [Finite F] [CharP F 2] in
theorem conj_uMat_entry (g : GL (Fin 3) F) (v : Fin 2 → F) (j : Fin 2) :
    ((g : Matrix (Fin 3) (Fin 3) F) * (uMat v : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 0 j.succ = (rhoMatG g *ᵥ v) j := by
  have h := congrFun (congrFun (coe_mul_inv_GL g) 0) j.succ
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at h
  fin_cases j <;>
  · simp [rhoMatG, coe_uMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] at h ⊢
    linear_combination h

theorem conj_iota0 (hF : Nat.card F = 4) {g : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F 0) : Subgroup (PGL3 F)) : Set (PGL3 F)))
    (v : Multiplicative (Fin 2 → F)) :
    ProjGenLinGroup.mk g * iota0 v * (ProjGenLinGroup.mk g)⁻¹ =
      iota0 (Multiplicative.ofAdd (rhoMatG g *ᵥ Multiplicative.toAdd v)) := by
  obtain ⟨r, hr, hgr⟩ := CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12.conj_radU hF hg
    (uMat_mem_radU (Multiplicative.toAdd v))
  have hm : (g : Matrix (Fin 3) (Fin 3) F) * (uMat (Multiplicative.toAdd v) :
      Matrix (Fin 3) (Fin 3) F) * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (r : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hgr
    simpa only [Units.val_mul, SpecialLinearGroup.coe_GL_coe_matrix] using this
  rw [iota0_apply, iota0_apply, ← map_inv, ← map_mul, ← map_mul, hgr, toAdd_ofAdd]
  congr 2
  rw [eq_uMat_of_mem_radU hr]
  congr 1
  funext j
  have e0 := conj_uMat_entry g (Multiplicative.toAdd v) 0
  have e1 := conj_uMat_entry g (Multiplicative.toAdd v) 1
  rw [hm] at e0 e1
  fin_cases j
  · simpa using e0
  · simpa using e1

omit [Finite F] [CharP F 2] in
theorem rhoMatG_mul_scalar (g : GL (Fin 3) F) (c : Fˣ) :
    rhoMatG (g * GeneralLinearGroup.scalar (Fin 3) c) = rhoMatG g := by
  ext i k
  rw [rhoMatG, rhoMatG, Matrix.of_apply, Matrix.of_apply, _root_.mul_inv_rev, ← map_inv,
    Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Units.val_inv_eq_inv_val]
  have hc : (c : F) ≠ 0 := c.ne_zero
  field_simp

omit [Finite F] [CharP F 2] in
theorem rhoMatG_eq_of_mk_eq {g g' : GL (Fin 3) F}
    (h : ProjGenLinGroup.mk g = ProjGenLinGroup.mk g') : rhoMatG g = rhoMatG g' := by
  obtain ⟨c, rfl⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  exact (rhoMatG_mul_scalar g c).symm

omit [Finite F] [CharP F 2] in
theorem matrix_ext_mulVec {M N : Matrix (Fin 2) (Fin 2) F} (h : ∀ v, M *ᵥ v = N *ᵥ v) :
    M = N := by
  ext i k
  have := congrFun (h (Pi.single k 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem rhoMatG_mul (hF : Nat.card F = 4) {g h : GL (Fin 3) F}
    (hg : ProjGenLinGroup.mk g ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F 0) : Subgroup (PGL3 F)) : Set (PGL3 F)))
    (hh : ProjGenLinGroup.mk h ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F 0) : Subgroup (PGL3 F)) : Set (PGL3 F))) :
    rhoMatG (g * h) = rhoMatG g * rhoMatG h := by
  refine matrix_ext_mulVec fun v => ?_
  have hgh : ProjGenLinGroup.mk (g * h) ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F 0) : Subgroup (PGL3 F)) : Set (PGL3 F)) := by
    rw [map_mul]
    exact Subgroup.mul_mem _ hg hh
  have e1 := conj_iota0 hF hgh (Multiplicative.ofAdd v)
  rw [map_mul, _root_.mul_inv_rev,
    show ∀ a b c d : PGL3 F, a * b * c * (d * a⁻¹) = a * (b * c * d) * a⁻¹ from
      fun a b c d => by group, conj_iota0 hF hh, conj_iota0 hF hg] at e1
  have := congrArg Multiplicative.toAdd (iota0_injective e1)
  simp only [toAdd_ofAdd] at this
  rw [← Matrix.mulVec_mulVec]
  exact this.symm

omit [Finite F] [CharP F 2] in
theorem rhoMatG_one : rhoMatG (1 : GL (Fin 3) F) = 1 := by
  ext i k
  simp only [rhoMatG, Matrix.of_apply, inv_one, Units.val_one, Matrix.one_apply_eq, one_mul,
    Matrix.one_apply, Fin.succ_inj]
  by_cases hik : i = k
  · subst hik; simp
  · simp [hik, Ne.symm hik]

end CFSG.Quasithin.H13.Ch4.B414.M

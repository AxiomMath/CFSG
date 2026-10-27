module

public import CFSG.LocalAnalysis.UniquenessCase.UC22L3UniBasic
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups.L3Eps
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped MatrixGroups

variable {p f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData p f F)

local notation "𝟙" => ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

abbrev CenU : Subgroup (primeFormUnitary h 𝟙) :=
  (L3Lin.CenG F).comap (primeFormUnitary h 𝟙).subtype

@[expose] def toCenG : ↥(CenU h) →* ↥(L3Lin.CenG F) :=
  ((primeFormUnitary h 𝟙).subtype.subgroupComap (L3Lin.CenG F))

theorem coe_toCenG (A : ↥(CenU h)) : (toCenG h A : GL (Fin 3) F) = A := rfl

theorem commute_of_conjHom {A T : primeFormUnitary h 𝟙}
    (hT : ((T : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace ≠ 0)
    (hAT : primeFormConjHom h 𝟙 A * primeFormConjHom h 𝟙 T =
      primeFormConjHom h 𝟙 T * primeFormConjHom h 𝟙 A) : A * T = T * A := by
  have h1 : primeFormConjHom h 𝟙 (A * T * A⁻¹ * T⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hAT]
    group
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one
    (by norm_num) h1
  have hconj : (A : GL (Fin 3) F) * T * (A : GL (Fin 3) F)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) c * T := by
    rw [← hc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have htr := congrArg (fun X : GL (Fin 3) F => (X : Matrix (Fin 3) (Fin 3) F).trace) hconj
  simp only [Units.val_mul, Matrix.trace_mul_cycle ((A : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F),
    Units.inv_mul, one_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.trace_mul_comm (Matrix.diagonal fun _ => (c : F))] at htr
  have hsc : (((T : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      Matrix.diagonal fun _ => (c : F)).trace =
      (c : F) * ((T : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace := by
    simp [Matrix.trace, Matrix.mul_diagonal, Finset.mul_sum, mul_comm]
  have hc1 : (c : F) = 1 := by
    have htr' := htr.trans hsc
    have hz : ((T : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).trace * (1 - (c : F)) = 0 := by
      linear_combination htr'
    exact (sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left hT)).symm
  have hc1' : c = 1 := Units.ext hc1
  rw [hc1', map_one, one_mul] at hconj
  apply Subtype.ext
  calc (A : GL (Fin 3) F) * T = (A : GL (Fin 3) F) * T * (A : GL (Fin 3) F)⁻¹ * A := by group
    _ = (T : GL (Fin 3) F) * A := by rw [hconj]

abbrev C : Subgroup (MulAut (primeFormP h 𝟙)) :=
  P h ⊓ centralizer ({e h ^ 2} : Set (MulAut (primeFormP h 𝟙)))

theorem conjHom_mem_C {A : primeFormUnitary h 𝟙} (hA : A ∈ CenU h) :
    primeFormConjHom h 𝟙 A ∈ C h := by
  refine Subgroup.mem_inf.2 ⟨⟨A, rfl⟩, ?_⟩
  rw [mem_centralizer_singleton_iff, e_sq, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 hA

@[expose] def piC : ↥(CenU h) →* ↥(C h) :=
  ((primeFormConjHom h 𝟙).comp (CenU h).subtype).codRestrict (C h)
    (fun A => conjHom_mem_C h A.2)

theorem coe_piC (A : ↥(CenU h)) : (piC h A : MulAut (primeFormP h 𝟙)) =
    primeFormConjHom h 𝟙 A := rfl

theorem piC_surjective : Function.Surjective (piC h) := by
  rintro ⟨x, hx⟩
  obtain ⟨⟨A, rfl⟩, hx⟩ := Subgroup.mem_inf.1 hx
  rw [mem_centralizer_singleton_iff, e_sq] at hx
  have hA : (A : GL (Fin 3) F) * L3Lin.dG = L3Lin.dG * (A : GL (Fin 3) F) := by
    have hc := commute_of_conjHom h (A := A) (T := d h)
      (by rw [coe_d, L3Lin.trace_dG]; exact neg_ne_zero.2 one_ne_zero) hx
    exact congrArg Subtype.val hc
  exact ⟨⟨A, mem_centralizer_singleton_iff.2 hA⟩, rfl⟩

theorem commute_of_piC (h2 : (2 : F) ≠ 0) {A B : ↥(CenU h)}
    (hAB : piC h A * piC h B = piC h B * piC h A) : A * B = B * A := by
  have h1 : primeFormConjHom h 𝟙 ((A * B * A⁻¹ * B⁻¹ : ↥(CenU h)) :
      primeFormUnitary h 𝟙) = 1 := by
    have hAB' := congrArg Subtype.val hAB
    simp only [Subgroup.coe_mul, coe_piC] at hAB'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hAB']
    group
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one
    (by norm_num) h1
  have hcc : (toCenG h (A * B * A⁻¹ * B⁻¹) : GL (Fin 3) F) =
      GeneralLinearGroup.scalar (Fin 3) c := hc
  have hc1 : c = 1 := L3Lin.eq_one_of_scalar_corner h2 hcc (by
    simp only [map_mul, map_inv]
    rw [mul_right_comm ((L3Lin.cornerHom h2) (toCenG h A)), mul_inv_cancel, one_mul,
      mul_inv_cancel])
  have hcomm : A * B * A⁻¹ * B⁻¹ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hc, hc1, map_one]
    rfl
  calc A * B = (A * B * A⁻¹ * B⁻¹) * (B * A) := by group
    _ = B * A := by rw [hcomm, one_mul]

theorem ker_piC_le (h2 : (2 : F) ≠ 0) : (piC h).ker ≤
    ((Matrix.ProjGenLinGroup.mk).comp ((L3Lin.blkHom h2).comp (toCenG h))).ker := by
  intro A hA
  rw [MonoidHom.mem_ker] at hA ⊢
  have h1 : primeFormConjHom h 𝟙 A = 1 := congrArg Subtype.val hA
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one
    (by norm_num) h1
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Matrix.ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨c, Units.ext ?_⟩
  rw [L3Lin.coe_blkHom, coe_toCenG, hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L3Lin.blk]

@[expose] def rho (h2 : (2 : F) ≠ 0) : ↥(C h) →* PGL(Fin 2, F) :=
  (piC h).liftOfSurjective (piC_surjective h)
    ⟨(Matrix.ProjGenLinGroup.mk).comp ((L3Lin.blkHom h2).comp (toCenG h)), ker_piC_le h h2⟩

theorem rho_piC (h2 : (2 : F) ≠ 0) (A : ↥(CenU h)) :
    rho h h2 (piC h A) = Matrix.ProjGenLinGroup.mk (L3Lin.blkHom h2 (toCenG h A)) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ A

theorem Kb_le (hq : Odd (p ^ f)) : Kb h hq ≤ C h := by
  rintro _ ⟨x, hx, rfl⟩
  refine Subgroup.mem_inf.2 ⟨I_le_P h ⟨x, rfl⟩, ?_⟩
  rw [mem_centralizer_singleton_iff, e, ← map_pow, ← QuotientGroup.mk_pow, ← map_mul,
    ← map_mul]
  have hxC := Uni.levS_le_centralizer (θ := proj h) hq hx
  rw [mem_centralizer_singleton_iff, proj_dU] at hxC
  exact congrArg MulAut.conj hxC

abbrev Zb : Subgroup (MulAut (primeFormP h 𝟙)) := (center ↥(C h)).map (C h).subtype

theorem mem_Zb (x : MulAut (primeFormP h 𝟙)) : x ∈ Zb h ↔ x ∈ C h ∧
    ∀ y ∈ C h, x * y = y * x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, fun y hy => ?_⟩
    have he := (Subgroup.mem_center_iff.1 ha) (⟨y, hy⟩ : ↥(C h))
    exact (congrArg Subtype.val he).symm
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change (⟨x, hx⟩ : ↥(C h)) ∈ center ↥(C h)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y y.2).symm

@[expose] def normalizedBlock (h2 : (2 : F) ≠ 0) : ↥(CenU h) →* GL (Fin 2) F where
  toFun A := GeneralLinearGroup.scalar (Fin 2) ((L3Lin.cornerHom h2 (toCenG h A))⁻¹) *
    L3Lin.blkHom h2 (toCenG h A)
  map_one' := by simp only [map_one, inv_one, one_mul]
  map_mul' A B := by
    simp only [map_mul, _root_.mul_inv_rev]
    let a := GeneralLinearGroup.scalar (Fin 2) ((L3Lin.cornerHom h2 (toCenG h A))⁻¹)
    let b := GeneralLinearGroup.scalar (Fin 2) ((L3Lin.cornerHom h2 (toCenG h B))⁻¹)
    let x := L3Lin.blkHom h2 (toCenG h A)
    let y := L3Lin.blkHom h2 (toCenG h B)
    change b * a * (x * y) = a * x * (b * y)
    have hba : b * a = a * b := GeneralLinearGroup.scalar_commute _ _
    have hbx : b * x = x * b := GeneralLinearGroup.scalar_commute _ _
    calc b * a * (x * y) = a * (b * x) * y := by rw [hba]; group
      _ = a * x * (b * y) := by rw [hbx]; group

theorem coe_normalizedBlock (h2 : (2 : F) ≠ 0) (A : ↥(CenU h)) :
    ((normalizedBlock h h2 A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (((L3Lin.cornerHom h2 (toCenG h A))⁻¹ : Fˣ) : F) •
        L3Lin.blk (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  change ((GeneralLinearGroup.scalar (Fin 2) ((L3Lin.cornerHom h2 (toCenG h A))⁻¹) *
    L3Lin.blkHom h2 (toCenG h A) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = _
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, L3Lin.coe_blkHom,
    coe_toCenG]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem normalizedBlock_unitary (h2 : (2 : F) ≠ 0) (A : ↥(CenU h)) :
    normalizedBlock h h2 A ∈ primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hA := (A : primeFormUnitary h 𝟙).2
  have hA' : ((((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map h.bar)ᵀ *
    (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    simpa only [mem_primeFormUnitary, Units.val_one, Matrix.mul_one] using hA
  rw [mem_primeFormUnitary, Matrix.mul_one]
  obtain ⟨h02, h12, h20, h21⟩ := L3Lin.entries_of_mem_CenG h2 (toCenG h A).2
  let M := (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  change M 0 2 = 0 at h02
  change M 1 2 = 0 at h12
  change M 2 0 = 0 at h20
  change M 2 1 = 0 at h21
  change (M.map h.bar)ᵀ * M = 1 at hA'
  have hcorner : h.bar (M 2 2) * M 2 2 = 1 := by
    have he := congrFun (congrFun hA' 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h02, h12] using he
  have hblock : ((L3Lin.blk M).map h.bar)ᵀ * L3Lin.blk M = 1 := by
    ext i j
    have he := congrFun (congrFun hA' i.castSucc) j.castSucc
    fin_cases i <;> fin_cases j <;>
      simpa [L3Lin.blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, h20, h21] using he
  rw [coe_normalizedBlock]
  have hc : h.bar ((((L3Lin.cornerHom h2 (toCenG h A))⁻¹ : Fˣ) : F)) *
      (((L3Lin.cornerHom h2 (toCenG h A))⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, L3Lin.coe_cornerHom, coe_toCenG,
      hcorner, inv_one]
  let c : F := (((L3Lin.cornerHom h2 (toCenG h A))⁻¹ : Fˣ) : F)
  have hmap : (c • L3Lin.blk M).map h.bar = h.bar c • (L3Lin.blk M).map h.bar := by
    ext i j
    simp [c, Matrix.smul_apply, smul_eq_mul]
  change ((c • L3Lin.blk M).map h.bar)ᵀ * (c • L3Lin.blk M) = 1
  rw [hmap, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hblock, hc, one_smul]

theorem ker_piC_le_normalizedBlock (h2 : (2 : F) ≠ 0) :
    (piC h).ker ≤ (normalizedBlock h h2).ker := by
  intro A hA
  have h1 : primeFormConjHom h 𝟙 A = 1 := congrArg Subtype.val hA
  obtain ⟨c, -, hc⟩ := eq_scalar_of_primeFormConjHom_eq_one h isPrimeFormGram_one
    (by norm_num) h1
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [coe_normalizedBlock]
  have hc' : L3Lin.cornerHom h2 (toCenG h A) = c := by
    apply Units.ext
    rw [L3Lin.coe_cornerHom, coe_toCenG, hc]
    simp
  rw [hc', hc]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [L3Lin.blk, GeneralLinearGroup.coe_scalar]

@[expose] def psi (h2 : (2 : F) ≠ 0) : ↥(C h) →* GL (Fin 2) F :=
  (piC h).liftOfSurjective (piC_surjective h)
    ⟨normalizedBlock h h2, ker_piC_le_normalizedBlock h h2⟩

theorem psi_piC (h2 : (2 : F) ≠ 0) (A : ↥(CenU h)) :
    psi h h2 (piC h A) = normalizedBlock h h2 A :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ A

theorem psi_unitary (h2 : (2 : F) ≠ 0) (x : ↥(C h)) :
    psi h h2 x ∈ primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) := by
  obtain ⟨A, rfl⟩ := piC_surjective h x
  rw [psi_piC]
  exact normalizedBlock_unitary h h2 A

theorem conjHom_eq_one_of_scalar {A : primeFormUnitary h 𝟙} {c : Fˣ}
    (hc : h.norm (c : F) = 1) (hA : (A : GL (Fin 3) F) = GeneralLinearGroup.scalar (Fin 3) c) :
    primeFormConjHom h 𝟙 A = 1 := by
  have he := (primeFormPsi_eq_one_iff h isPrimeFormGram_one (by norm_num) ⟨A, 1⟩).2
    ⟨rfl, c, hc, hA⟩
  simpa only [primeFormPsi_apply, map_one, mul_one] using he

theorem normalizedBlock_eq_one_imp_piC (h2 : (2 : F) ≠ 0) (A : ↥(CenU h))
    (hA : normalizedBlock h h2 A = 1) : piC h A = 1 := by
  let c := L3Lin.cornerHom h2 (toCenG h A)
  have hb : L3Lin.blkHom h2 (toCenG h A) = GeneralLinearGroup.scalar (Fin 2) c := by
    have he : GeneralLinearGroup.scalar (Fin 2) c⁻¹ * L3Lin.blkHom h2 (toCenG h A) = 1 := hA
    have he' := congrArg (fun B : GL (Fin 2) F => GeneralLinearGroup.scalar (Fin 2) c * B) he
    simpa only [map_inv, ← mul_assoc, mul_inv_cancel, one_mul, mul_one] using he'
  have hc : (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F)) = GeneralLinearGroup.scalar (Fin 3) c := by
    obtain ⟨h02, h12, h20, h21⟩ := L3Lin.entries_of_mem_CenG h2 (toCenG h A).2
    have he := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F)) hb
    rw [L3Lin.coe_blkHom, coe_toCenG, GeneralLinearGroup.coe_scalar] at he
    have he22 : (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = c :=
      (L3Lin.coe_cornerHom h2 (toCenG h A)).symm
    change ((((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) = 0 at h02
    change ((((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2) = 0 at h12
    change ((((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0) = 0 at h20
    change ((((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1) = 0 at h21
    have he00 := congrFun (congrFun he 0) 0
    have he01 := congrFun (congrFun he 0) 1
    have he10 := congrFun (congrFun he 1) 0
    have he11 := congrFun (congrFun he 1) 1
    simp only [L3Lin.blk, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.cons_val', Matrix.empty_val', Matrix.scalar_apply,
      Matrix.diagonal_apply] at he00 he01 he10 he11
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.coe_scalar, h02, h12, h20, h21, he22, he00, he01, he10, he11]
  have hn : h.norm (c : F) = 1 := by
    have he := (A : primeFormUnitary h 𝟙).2
    rw [mem_primeFormUnitary] at he
    have h00 := congrFun (congrFun he 0) 0
    rw [hc] at h00
    have hnorm : h.bar (c : F) * (c : F) = 1 := by
      simpa [GeneralLinearGroup.coe_scalar] using h00
    exact (mul_comm (c : F) (h.bar (c : F))).trans hnorm
  apply Subtype.ext
  exact conjHom_eq_one_of_scalar h hn hc

theorem psi_injective (h2 : (2 : F) ≠ 0) : Function.Injective (psi h h2) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨A, rfl⟩ := piC_surjective h x
  have he : normalizedBlock h h2 A = 1 := by
    rw [← psi_piC]
    exact hx
  exact normalizedBlock_eq_one_imp_piC h h2 A he

@[expose] def blockU : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) →* primeFormUnitary h 𝟙 :=
  ((CFSG.RankThree.SubgroupLists.blockGL3).comp
    (primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F)).subtype).codRestrict _ (fun B => by
      rw [mem_primeFormUnitary]
      have hB := B.2
      rw [mem_primeFormUnitary, Matrix.mul_one] at hB
      change ((CFSG.RankThree.SubgroupLists.leviMat
        (((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))).map h.bar)ᵀ * 𝟙 *
          CFSG.RankThree.SubgroupLists.leviMat (((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) = 𝟙
      simp only [Units.val_one, Matrix.mul_one, Uni.leviMat_unitary, hB,
        CFSG.RankThree.SubgroupLists.leviMat_one])

theorem blockU_mem_CenU (B : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F)) :
    blockU h B ∈ CenU h := by
  change CFSG.RankThree.SubgroupLists.blockGL3 (B : GL (Fin 2) F) ∈ L3Lin.CenG F
  rw [mem_centralizer_singleton_iff]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, CFSG.RankThree.SubgroupLists.coe_blockGL3, L3Lin.coe_dG,
    Uni.dNeg_coe_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.RankThree.SubgroupLists.leviMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def blockC : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) →* ↥(C h) :=
  (piC h).comp ((blockU h).codRestrict (CenU h) (blockU_mem_CenU h))

theorem psi_blockC (h2 : (2 : F) ≠ 0)
    (B : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F)) :
    psi h h2 (blockC h B) = (B : GL (Fin 2) F) := by
  rw [blockC, MonoidHom.comp_apply, psi_piC]
  have hc : L3Lin.cornerHom h2 (toCenG h ⟨blockU h B, blockU_mem_CenU h B⟩) = 1 := by
    apply Units.ext
    rw [L3Lin.coe_cornerHom, coe_toCenG]
    rfl
  change GeneralLinearGroup.scalar (Fin 2)
    ((L3Lin.cornerHom h2 (toCenG h ⟨blockU h B, blockU_mem_CenU h B⟩))⁻¹) *
      L3Lin.blkHom h2 (toCenG h ⟨blockU h B, blockU_mem_CenU h B⟩) = _
  rw [hc, inv_one, map_one, one_mul]
  apply Units.ext
  rw [L3Lin.coe_blkHom, coe_toCenG]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem rho_eq_mk_psi (h2 : (2 : F) ≠ 0) (x : ↥(C h)) :
    rho h h2 x = Matrix.ProjGenLinGroup.mk (psi h h2 x) := by
  obtain ⟨A, rfl⟩ := piC_surjective h x
  rw [rho_piC, psi_piC]
  change Matrix.ProjGenLinGroup.mk (L3Lin.blkHom h2 (toCenG h A)) =
    Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 2)
      ((L3Lin.cornerHom h2 (toCenG h A))⁻¹) * L3Lin.blkHom h2 (toCenG h A))
  rw [map_mul]
  have he : Matrix.ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 2)
      ((L3Lin.cornerHom h2 (toCenG h A))⁻¹)) = 1 := by
    rw [Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  rw [he, one_mul]

theorem psi_Kb (h2 : (2 : F) ≠ 0) (hq : Odd (p ^ f)) (x : ↥(C h)) :
    (x : MulAut (primeFormP h 𝟙)) ∈ Kb h hq ↔ psi h h2 x ∈ unitarySU p f F 2 := by
  constructor
  · rintro ⟨y, ⟨B, hB⟩, hxy⟩
    let Bu : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) :=
      ⟨B, by
        rw [mem_primeFormUnitary, Matrix.mul_one]
        exact ((mem_unitarySU_iff h).1 B.2).2⟩
    have hbc : blockC h Bu = x := by
      apply Subtype.ext
      change primeFormConjHom h 𝟙 (blockU h Bu) = (x : MulAut (primeFormP h 𝟙))
      have hc : blockU h Bu = ⟨suEquiv h (Uni.levU hq.pos B),
          (suEquiv h (Uni.levU hq.pos B)).2.1⟩ := Subtype.ext rfl
      rw [hc, primeFormConjHom_eq_conj]
      exact (congrArg MulAut.conj hB).trans hxy
    rw [← hbc, psi_blockC]
    exact B.2
  · intro hx
    let B : unitarySU p f F 2 := ⟨psi h h2 x, hx⟩
    let Bu : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) := ⟨B, psi_unitary h h2 x⟩
    have hbc : blockC h Bu = x := psi_injective h h2 (psi_blockC h h2 Bu)
    refine ⟨proj h (Uni.levU hq.pos B), ⟨B, rfl⟩, ?_⟩
    rw [← hbc]
    change MulAut.conj (proj h (Uni.levU hq.pos B)) = primeFormConjHom h 𝟙 (blockU h Bu)
    have hc : blockU h Bu = ⟨suEquiv h (Uni.levU hq.pos B),
        (suEquiv h (Uni.levU hq.pos B)).2.1⟩ := Subtype.ext rfl
    rw [hc, primeFormConjHom_eq_conj]
    rfl

theorem rho_eq_one (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ p ^ f) (x : ↥(C h)) :
    rho h h2 x = 1 ↔ (x : MulAut (primeFormP h 𝟙)) ∈ Zb h := by
  rw [rho_eq_mk_psi, Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar,
    mem_Zb]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨x.2, fun y hy => ?_⟩
    apply Subtype.ext_iff.1 (psi_injective h h2 (show psi h h2 (x * ⟨y, hy⟩) =
        psi h h2 (⟨y, hy⟩ * x) from ?_))
    rw [map_mul, map_mul, ← hc]
    exact GeneralLinearGroup.scalar_commute _ _
  · rintro ⟨-, hx⟩
    obtain ⟨A, hA⟩ := piC_surjective h x
    have hc : ∀ B : ↥(unitarySU p f F 2),
        (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            CFSG.RankThree.SubgroupLists.leviMat (Uni.matU B) =
          CFSG.RankThree.SubgroupLists.leviMat (Uni.matU B) *
            (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      intro B
      let Bu : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) :=
        ⟨B, by rw [mem_primeFormUnitary, Matrix.mul_one]; exact ((mem_unitarySU_iff h).1 B.2).2⟩
      have hcomm : piC h A * blockC h Bu = blockC h Bu * piC h A := by
        apply Subtype.ext
        rw [hA]
        exact hx _ (blockC h Bu).2
      have he := commute_of_piC h h2 (A := A) (B := ⟨blockU h Bu, blockU_mem_CenU h Bu⟩) hcomm
      exact congrArg (fun A : ↥(CenU h) =>
        (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) he
    obtain ⟨h01, h10, -, -, -, -, h00⟩ := Uni.form_of_commute_all h h5 hc
    let c := L3Lin.cornerHom h2 (toCenG h A)
    let a : F := (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0
    have ha0 : a ≠ 0 := by
      have he := L3Lin.blkHom h2 (toCenG h A) |>.isUnit.map Matrix.detMonoidHom |>.ne_zero
      change (((L3Lin.blkHom h2 (toCenG h A) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det) ≠ 0 at he
      rw [L3Lin.coe_blkHom, coe_toCenG] at he
      intro hz
      have hz' : (((A : primeFormUnitary h 𝟙) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 = 0 := hz
      exact he (by simp [Matrix.det_fin_two, L3Lin.blk, hz', h01, h10])
    refine ⟨c⁻¹ * Units.mk0 a ha0, ?_⟩
    apply Units.ext
    rw [← hA, psi_piC, coe_normalizedBlock, GeneralLinearGroup.coe_scalar]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [c, a, L3Lin.blk, h01, h10, h00]

theorem eq_one_of_mem_Kb_Zb (h2 : (2 : F) ≠ 0) (hq : Odd (p ^ f)) (h5 : 5 ≤ p ^ f)
    {x : MulAut (primeFormP h 𝟙)} (hx : x ∈ Kb h hq) (hz : x ∈ Zb h)
    (hodd : Odd (orderOf x)) : x = 1 := by
  let xc : ↥(C h) := ⟨x, Kb_le h hq hx⟩
  have hB : psi h h2 xc ∈ unitarySU p f F 2 := (psi_Kb h h2 hq xc).1 hx
  let B : unitarySU p f F 2 := ⟨psi h h2 xc, hB⟩
  have hc : ∀ B' : unitarySU p f F 2, B' * B = B * B' := by
    intro B'
    let B'u : primeFormUnitary h (1 : Matrix (Fin 2) (Fin 2) F) :=
      ⟨B', by rw [mem_primeFormUnitary, Matrix.mul_one]; exact ((mem_unitarySU_iff h).1 B'.2).2⟩
    have hcomm := ((mem_Zb h x).1 hz).2 _ (blockC h B'u).2
    have he : blockC h B'u * xc = xc * blockC h B'u := Subtype.ext hcomm.symm
    apply Subtype.ext
    have hψ := congrArg (psi h h2) he
    simpa only [map_mul, psi_blockC, Subgroup.coe_mul, B'u, B, Subtype.coe_mk] using hψ
  rcases Uni.su2_center h h5 hc with hB1 | hBneg
  · have hψ1 : psi h h2 xc = 1 := congrArg Subtype.val hB1
    have hx1 : xc = 1 := (map_eq_one_iff _ (psi_injective h h2)).1 hψ1
    exact congrArg Subtype.val hx1
  · have hψsq : (psi h h2 xc) ^ 2 = 1 := by
      change (B : GL (Fin 2) F) ^ 2 = 1
      rw [hBneg]
      have he : (Uni.negI h : unitarySU p f F 2) ^ 2 = 1 := by
        apply Uni.matU_ext
        rw [sq, Uni.matU_mul, Uni.matU_negI, Uni.matU_one, neg_mul_neg, one_mul]
      exact congrArg Subtype.val he
    have hx2 : x ^ 2 = 1 := congrArg Subtype.val
      ((map_eq_one_iff _ (psi_injective h h2)).1 (by rw [map_pow]; exact hψsq))
    have hord : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
      (Nat.coprime_two_right.2 hodd) (orderOf_dvd_of_pow_eq_one hx2)
    exact orderOf_eq_one_iff.1 hord

theorem mem_Kb_of_inv (h2 : (2 : F) ≠ 0) (hq : Odd (p ^ f))
    (x w : ↥(C h)) (hx : Odd (orderOf x)) (hinv : w * x * w⁻¹ = x⁻¹) :
    (x : MulAut (primeFormP h 𝟙)) ∈ Kb h hq := by
  rw [psi_Kb]
  have hu := psi_unitary h h2 x
  rw [mem_unitarySU_iff h]
  refine ⟨?_, by simpa only [mem_primeFormUnitary, Matrix.mul_one] using hu⟩
  have he := congrArg (fun x : ↥(C h) => GeneralLinearGroup.det (psi h h2 x)) hinv
  simp only [map_mul, map_inv] at he
  have he' : GeneralLinearGroup.det (psi h h2 x) = (GeneralLinearGroup.det (psi h h2 x))⁻¹ := by
    calc GeneralLinearGroup.det (psi h h2 x) = GeneralLinearGroup.det (psi h h2 w) *
        GeneralLinearGroup.det (psi h h2 x) * (GeneralLinearGroup.det (psi h h2 w))⁻¹ := by
          rw [mul_comm (GeneralLinearGroup.det (psi h h2 w)), mul_inv_cancel_right]
      _ = _ := he
  have hsq : (GeneralLinearGroup.det (psi h h2 x)) ^ 2 = 1 := by
    calc (GeneralLinearGroup.det (psi h h2 x)) ^ 2 =
        GeneralLinearGroup.det (psi h h2 x) * (GeneralLinearGroup.det (psi h h2 x))⁻¹ := by rw [← he', sq]
      _ = 1 := mul_inv_cancel _
  have ho : Odd (orderOf (GeneralLinearGroup.det (psi h h2 x))) :=
    Odd.of_dvd_nat hx (orderOf_map_dvd ((GeneralLinearGroup.det).comp (psi h h2)) x)
  have h1 : GeneralLinearGroup.det (psi h h2 x) = 1 := orderOf_eq_one_iff.1
    (Nat.Coprime.eq_one_of_dvd (Nat.coprime_two_right.2 ho) (orderOf_dvd_of_pow_eq_one hsq))
  exact congrArg Units.val h1

theorem isCyclic_Zb (h2 : (2 : F) ≠ 0) (h5 : 5 ≤ p ^ f) : IsCyclic ↥(Zb h) := by
  have : Finite F := h.finite
  let j : ↥(Zb h) →* ↥(C h) := Subgroup.inclusion (by
    intro x hx
    exact ((mem_Zb h x).1 hx).1)
  have hsc : ∀ x : ↥(Zb h), ∃ c : Fˣ, GeneralLinearGroup.scalar (Fin 2) c = psi h h2 (j x) := by
    intro x
    have hx := (rho_eq_one h h2 h5 (j x)).2 x.2
    rw [rho_eq_mk_psi, Matrix.ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hx
    exact hx
  let s : ↥(Zb h) → Fˣ := fun x => Classical.choose (hsc x)
  have hs : ∀ x, GeneralLinearGroup.scalar (Fin 2) (s x) = psi h h2 (j x) :=
    fun x => Classical.choose_spec (hsc x)
  let χ : ↥(Zb h) →* Fˣ :=
    { toFun := s
      map_one' := by
        apply Units.ext
        have he : GeneralLinearGroup.scalar (Fin 2) (s 1) = 1 := by rw [hs, map_one, map_one]
        have he00 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) he
        simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
          if_pos, Units.val_one, Matrix.one_apply_eq] using he00
      map_mul' a b := by
        apply Units.ext
        have he : GeneralLinearGroup.scalar (Fin 2) (s (a * b)) =
            GeneralLinearGroup.scalar (Fin 2) (s a * s b) := by
          rw [hs, map_mul, map_mul, map_mul, hs, hs]
        have he00 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) he
        simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
          if_pos] using he00 }
  apply isCyclic_of_injective χ
  intro a b hab
  have hab' : psi h h2 (j a) = psi h h2 (j b) := by
    rw [← hs, ← hs]
    exact congrArg (GeneralLinearGroup.scalar (Fin 2)) hab
  apply Subtype.ext
  exact congrArg (fun x : ↥(C h) => (x : MulAut (primeFormP h 𝟙))) ((psi_injective h h2) hab')

end CFSG.LocalAnalysis.UniquenessCase.UC22.L3Uni

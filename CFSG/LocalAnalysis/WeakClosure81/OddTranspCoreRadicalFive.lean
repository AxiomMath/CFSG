module

public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCoreRadicalDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenNineDefs
import CFSG.LocalAnalysis.WeakClosure81.SevenNineOrthFrameFive
import CFSG.Quasithin.Recognition.L34AmalgamIsoA5
import CFSG.Quasithin.Recognition.J2RecCzIso
import CFSG.Timmesfeld.Exceptional.DeepWorldCFiber
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
import CFSG.Quasithin.Vol2.Ch6Sec1Lem25OddB
import CFSG.GroupTheory.QuotientCoreFacts
import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5Inputs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreRadical

open Matrix CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open CFSG.Quasithin CFSG.Quasithin.L34Amalgam CFSG.Quasithin.J2Cz CFSG.CosetTable
open CFSG.GroupTheory CFSG.LocalAnalysis.WeakClosure81.SevenK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def fiveGram4 : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![(-2 : ZMod 5), 1, 0, 0; 1, -2, 2, 0; 0, 2, -2, 0; 0, 0, 0, 1]

private def fiveT1Mat : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![(-1 : ZMod 5), 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def fiveT2Mat : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![1, 0, 0, 0; 1, (-1 : ZMod 5), 2, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def fiveT3Mat : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 2, (-1 : ZMod 5), 0; 0, 0, 0, 1]

private theorem fiveT1Mat_det : fiveT1Mat.det ≠ 0 := by decide
private theorem fiveT2Mat_det : fiveT2Mat.det ≠ 0 := by decide
private theorem fiveT3Mat_det : fiveT3Mat.det ≠ 0 := by decide

private noncomputable def fiveT1 : GL (Fin 4) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero fiveT1Mat fiveT1Mat_det

private noncomputable def fiveT2 : GL (Fin 4) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero fiveT2Mat fiveT2Mat_det

private noncomputable def fiveT3 : GL (Fin 4) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero fiveT3Mat fiveT3Mat_det

private theorem fiveT1_coe : (fiveT1 : Matrix (Fin 4) (Fin 4) (ZMod 5)) = fiveT1Mat :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
private theorem fiveT2_coe : (fiveT2 : Matrix (Fin 4) (Fin 4) (ZMod 5)) = fiveT2Mat :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
private theorem fiveT3_coe : (fiveT3 : Matrix (Fin 4) (Fin 4) (ZMod 5)) = fiveT3Mat :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private def fiveTM : Fin 3 → Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  ![fiveT1Mat, fiveT2Mat, fiveT3Mat]

private noncomputable def fiveTMGL : Fin 3 → GL (Fin 4) (ZMod 5) := ![fiveT1, fiveT2, fiveT3]

private theorem fiveTMGL_zero : fiveTMGL 0 = fiveT1 := rfl
private theorem fiveTMGL_coe (i : Fin 3) :
    (fiveTMGL i : Matrix (Fin 4) (Fin 4) (ZMod 5)) = fiveTM i := by
  fin_cases i <;> rfl

private theorem fiveT1_sq : fiveT1 * fiveT1 = 1 :=
  Units.ext (by simpa [fiveT1_coe, Matrix.GeneralLinearGroup.coe_one] using
    (show fiveT1Mat * fiveT1Mat = 1 by decide))

private theorem fiveT2_sq : fiveT2 * fiveT2 = 1 :=
  Units.ext (by simpa [fiveT2_coe, Matrix.GeneralLinearGroup.coe_one] using
    (show fiveT2Mat * fiveT2Mat = 1 by decide))

private theorem fiveT3_sq : fiveT3 * fiveT3 = 1 :=
  Units.ext (by simpa [fiveT3_coe, Matrix.GeneralLinearGroup.coe_one] using
    (show fiveT3Mat * fiveT3Mat = 1 by decide))

private theorem fiveT12 : (fiveT1 * fiveT2) ^ 3 = 1 :=
  Units.ext (by simpa [Units.val_pow_eq_pow_val, fiveT1_coe, fiveT2_coe,
    Matrix.GeneralLinearGroup.coe_one] using (show (fiveT1Mat * fiveT2Mat) ^ 3 = 1 by decide))

private theorem fiveT23 : (fiveT2 * fiveT3) ^ 5 = 1 :=
  Units.ext (by simpa [Units.val_pow_eq_pow_val, fiveT2_coe, fiveT3_coe,
    Matrix.GeneralLinearGroup.coe_one] using (show (fiveT2Mat * fiveT3Mat) ^ 5 = 1 by decide))

private theorem fiveT32 : (fiveT3 * fiveT2) ^ 5 = 1 :=
  Units.ext (by simpa [Units.val_pow_eq_pow_val, fiveT3_coe, fiveT2_coe,
    Matrix.GeneralLinearGroup.coe_one] using (show (fiveT3Mat * fiveT2Mat) ^ 5 = 1 by decide))

private theorem fiveT13 : fiveT1 * fiveT3 = fiveT3 * fiveT1 :=
  Units.ext (by simpa [fiveT1_coe, fiveT3_coe] using
    (show fiveT1Mat * fiveT3Mat = fiveT3Mat * fiveT1Mat by decide))

private theorem fiveT1_ne_fiveT2 : fiveT1 ≠ fiveT2 := fun h =>
  (show fiveT1Mat ≠ fiveT2Mat by decide) (by rw [← fiveT1_coe, ← fiveT2_coe, h])

private noncomputable def fiveAlpha : GL (Fin 4) (ZMod 5) := fiveT1 * fiveT3

private noncomputable def fiveBeta : GL (Fin 4) (ZMod 5) := fiveT1 * fiveT2

private def fiveZMat : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![(-1 : ZMod 5), 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]

private theorem fiveZMat_det : fiveZMat.det ≠ 0 := by decide

private noncomputable def fiveZ : GL (Fin 4) (ZMod 5) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero fiveZMat fiveZMat_det

private theorem fiveZ_coe : (fiveZ : Matrix (Fin 4) (Fin 4) (ZMod 5)) = fiveZMat :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem fiveZ_eq_pow : fiveZ = (fiveT1 * fiveT2 * fiveT3) ^ 5 := by
  apply Units.ext
  rw [fiveZ_coe]
  rw [show (↑((fiveT1 * fiveT2 * fiveT3) ^ 5) : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      (fiveT1Mat * fiveT2Mat * fiveT3Mat) ^ 5 by
    rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mul, fiveT1_coe, fiveT2_coe,
      fiveT3_coe]]
  exact (show (fiveT1Mat * fiveT2Mat * fiveT3Mat) ^ 5 = fiveZMat by decide).symm

private theorem fiveZ_sq : fiveZ * fiveZ = 1 :=
  Units.ext (by rw [Units.val_mul, fiveZ_coe, Matrix.GeneralLinearGroup.coe_one]; decide)

private theorem fiveZ_ne_one : fiveZ ≠ 1 := by
  intro h
  have := congrArg (fun g : GL (Fin 4) (ZMod 5) =>
    (g : Matrix (Fin 4) (Fin 4) (ZMod 5))) h
  rw [fiveZ_coe, Matrix.GeneralLinearGroup.coe_one] at this
  exact (show fiveZMat ≠ 1 by decide) this

private theorem fiveZ_det : Matrix.GeneralLinearGroup.det fiveZ = -1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, fiveZ_coe]
  decide

private theorem fiveZ_comm_T1 : fiveZ * fiveT1 = fiveT1 * fiveZ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, fiveZ_coe, fiveT1_coe]
  decide

private theorem fiveZ_comm_T2 : fiveZ * fiveT2 = fiveT2 * fiveZ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, fiveZ_coe, fiveT2_coe]
  decide

private theorem fiveZ_comm_T3 : fiveZ * fiveT3 = fiveT3 * fiveZ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, fiveZ_coe, fiveT3_coe]
  decide

private theorem fiveAlpha_sq : fiveAlpha * fiveAlpha = 1 := by
  rw [fiveAlpha]
  calc (fiveT1 * fiveT3) * (fiveT1 * fiveT3)
      = fiveT1 * (fiveT3 * fiveT1) * fiveT3 := by group
    _ = fiveT1 * (fiveT1 * fiveT3) * fiveT3 := by rw [fiveT13]
    _ = (fiveT1 * fiveT1) * (fiveT3 * fiveT3) := by group
    _ = 1 := by rw [fiveT1_sq, fiveT3_sq, one_mul]

private theorem fiveBeta_cube : fiveBeta ^ 3 = 1 := by
  rw [fiveBeta]; exact fiveT12

private theorem fiveAlphaBeta_pow_five : (fiveAlpha * fiveBeta) ^ 5 = 1 := by
  rw [fiveAlpha, fiveBeta, fiveT13]
  have h : fiveT3 * fiveT1 * (fiveT1 * fiveT2) = fiveT3 * fiveT2 := by
    calc fiveT3 * fiveT1 * (fiveT1 * fiveT2) = fiveT3 * (fiveT1 * fiveT1) * fiveT2 := by group
      _ = fiveT3 * fiveT2 := by rw [fiveT1_sq, mul_one]
  rw [h]
  exact fiveT32

private theorem fiveBeta_ne_one : fiveBeta ≠ 1 := by
  intro h
  apply fiveT1_ne_fiveT2
  rw [fiveBeta] at h
  calc fiveT1 = fiveT1 * 1 := (mul_one fiveT1).symm
    _ = fiveT1 * (fiveT2 * fiveT2) := by rw [fiveT2_sq]
    _ = (fiveT1 * fiveT2) * fiveT2 := by group
    _ = fiveT2 := by rw [h, one_mul]

private noncomputable def fiveG4 : Subgroup (GL (Fin 4) (ZMod 5)) :=
  Subgroup.closure {fiveT1, fiveT2, fiveT3}

private noncomputable def fiveC : Subgroup (GL (Fin 4) (ZMod 5)) :=
  Subgroup.closure {fiveAlpha, fiveBeta}

private noncomputable def fiveZG : fiveG4 := ⟨fiveZ, by
  rw [fiveZ_eq_pow]
  exact fiveG4.pow_mem (fiveG4.mul_mem (fiveG4.mul_mem
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    (Subgroup.subset_closure (by simp))) 5⟩

private noncomputable def fiveT1G : fiveG4 := ⟨fiveT1, Subgroup.subset_closure (by simp)⟩

private noncomputable def fiveT2G : fiveG4 := ⟨fiveT2, Subgroup.subset_closure (by simp)⟩

private noncomputable def fiveT3G : fiveG4 := ⟨fiveT3, Subgroup.subset_closure (by simp)⟩

private theorem fiveZ_center : fiveZG ∈ Subgroup.center fiveG4 := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have h : ∀ x (hx : x ∈ fiveG4), x * fiveZ = fiveZ * x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with rfl | rfl | rfl
        · exact fiveZ_comm_T1.symm
        · exact fiveZ_comm_T2.symm
        · exact fiveZ_comm_T3.symm
    | one => simp
    | mul y w _ _ ihy ihw =>
        calc (y * w) * fiveZ = y * (w * fiveZ) := by group
          _ = y * (fiveZ * w) := by rw [ihw]
          _ = (y * fiveZ) * w := by group
          _ = (fiveZ * y) * w := by rw [ihy]
          _ = fiveZ * (y * w) := by group
    | inv y _ ihy =>
        calc y⁻¹ * fiveZ = y⁻¹ * (fiveZ * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * fiveZ) * y⁻¹ := by rw [ihy]
          _ = fiveZ * y⁻¹ := by group
  exact h (g : GL (Fin 4) (ZMod 5)) g.2

private theorem fiveT1_conj_fiveT2 : (fiveT1G * fiveT2G) * fiveT1G * (fiveT1G * fiveT2G)⁻¹ =
    fiveT2G := by
  exact CFSG.RankThree.PartTwo.Sec7.conj_eq_of_orderOf_mul_eq_three
    (Subtype.ext (by simpa [fiveT1G] using fiveT1_sq))
    (Subtype.ext (by simpa [fiveT2G] using fiveT2_sq))
    (Subtype.ext (by simpa [fiveT1G, fiveT2G] using fiveT12))

private theorem fiveT2_conj_fiveT3 :
    ((fiveT2G * fiveT3G) ^ 2) * fiveT2G * ((fiveT2G * fiveT3G) ^ 2)⁻¹ = fiveT3G := by
  exact CFSG.Timmesfeld.Moufang.Deep.conj_eq_of_pow_five (a := fiveT2G) (b := fiveT3G)
    (Subtype.ext (by simpa [fiveT2G] using fiveT2_sq))
    (Subtype.ext (by simpa [fiveT3G] using fiveT3_sq))
    (Subtype.ext (by simpa [fiveT2G, fiveT3G] using fiveT23))

private theorem fiveGen_top : Subgroup.closure ({fiveT1G, fiveT2G, fiveT3G} : Set fiveG4) = ⊤ := by
  have hK : (Subgroup.closure ({fiveT1G, fiveT2G, fiveT3G} : Set fiveG4)).map
      fiveG4.subtype = fiveG4 := by
    rw [MonoidHom.map_closure]
    have himg : fiveG4.subtype '' ({fiveT1G, fiveT2G, fiveT3G} : Set fiveG4) =
        ({fiveT1, fiveT2, fiveT3} : Set (GL (Fin 4) (ZMod 5))) := by
      ext x
      simp [fiveT1G, fiveT2G, fiveT3G]
    rw [himg]
    rfl
  have hT : (⊤ : Subgroup fiveG4).map fiveG4.subtype = fiveG4 := by
    rw [← Subgroup.subgroupOf_self (H := fiveG4), Subgroup.map_subgroupOf_eq_of_le le_rfl]
  exact Subgroup.map_subtype_inj.mp (hK.trans hT.symm)

private theorem fiveNormalClosure_top :
    Subgroup.normalClosure ({fiveT1G} : Set fiveG4) = ⊤ := by
  have hT2 : fiveT2G ∈ Subgroup.normalClosure ({fiveT1G} : Set fiveG4) := by
    rw [show fiveT2G = (fiveT1G * fiveT2G) * fiveT1G * (fiveT1G * fiveT2G)⁻¹ from
      (fiveT1_conj_fiveT2).symm]
    exact (Subgroup.normalClosure_normal).conj_mem fiveT1G
      (Subgroup.subset_normalClosure (by simp)) _
  have hT3 : fiveT3G ∈ Subgroup.normalClosure ({fiveT1G} : Set fiveG4) := by
    rw [show fiveT3G = ((fiveT2G * fiveT3G) ^ 2) * fiveT2G *
      ((fiveT2G * fiveT3G) ^ 2)⁻¹ from (fiveT2_conj_fiveT3).symm]
    exact (Subgroup.normalClosure_normal).conj_mem fiveT2G hT2 _
  refine le_antisymm le_top ?_
  rw [← fiveGen_top]
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl | rfl
  · exact Subgroup.subset_normalClosure (by simp)
  · exact hT2
  · exact hT3

private theorem fiveC_le_fiveG4 : fiveC ≤ fiveG4 := by
  rw [fiveC, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact fiveG4.mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  · exact fiveG4.mul_mem (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))

private theorem fiveAlpha_mem_C : fiveAlpha ∈ fiveC := Subgroup.subset_closure (by simp)
private theorem fiveBeta_mem_C : fiveBeta ∈ fiveC := Subgroup.subset_closure (by simp)

private theorem fiveZ_mul_T1_eq_word : fiveZ * fiveT1 =
    fiveAlpha * fiveBeta * fiveAlpha * (fiveBeta * fiveBeta) * fiveAlpha * fiveBeta *
      fiveAlpha * (fiveBeta * fiveBeta) * fiveAlpha * fiveBeta := by
  apply Units.ext
  rw [Units.val_mul, fiveZ_coe, fiveT1_coe]
  rw [show (↑(fiveAlpha * fiveBeta * fiveAlpha * (fiveBeta * fiveBeta) * fiveAlpha * fiveBeta *
      fiveAlpha * (fiveBeta * fiveBeta) * fiveAlpha * fiveBeta) :
        Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      (fiveT1Mat * fiveT3Mat) * (fiveT1Mat * fiveT2Mat) * (fiveT1Mat * fiveT3Mat) *
        ((fiveT1Mat * fiveT2Mat) * (fiveT1Mat * fiveT2Mat)) * (fiveT1Mat * fiveT3Mat) *
        (fiveT1Mat * fiveT2Mat) * (fiveT1Mat * fiveT3Mat) *
        ((fiveT1Mat * fiveT2Mat) * (fiveT1Mat * fiveT2Mat)) * (fiveT1Mat * fiveT3Mat) *
        (fiveT1Mat * fiveT2Mat) by
    simp only [Units.val_mul, fiveAlpha, fiveBeta, fiveT1_coe, fiveT2_coe, fiveT3_coe]]
  decide

private theorem fiveZ_mul_T1_mem_C : fiveZ * fiveT1 ∈ fiveC := by
  rw [fiveZ_mul_T1_eq_word]
  exact fiveC.mul_mem
    (fiveC.mul_mem
      (fiveC.mul_mem
        (fiveC.mul_mem
          (fiveC.mul_mem
            (fiveC.mul_mem
              (fiveC.mul_mem
                (fiveC.mul_mem
                  (fiveC.mul_mem fiveAlpha_mem_C fiveBeta_mem_C)
                  fiveAlpha_mem_C)
                (fiveC.mul_mem fiveBeta_mem_C fiveBeta_mem_C))
              fiveAlpha_mem_C)
            fiveBeta_mem_C)
          fiveAlpha_mem_C)
        (fiveC.mul_mem fiveBeta_mem_C fiveBeta_mem_C))
      fiveAlpha_mem_C)
    fiveBeta_mem_C

private theorem fiveT1_mem_sup : fiveT1 ∈ fiveC ⊔ Subgroup.zpowers fiveZ := by
  have h : fiveT1 = fiveZ * (fiveZ * fiveT1) := by
    rw [← mul_assoc, fiveZ_sq, one_mul]
  rw [h]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers fiveZ))
    (Subgroup.mem_sup_left fiveZ_mul_T1_mem_C)

private theorem fiveC_sup_fiveZ : fiveC ⊔ Subgroup.zpowers fiveZ = fiveG4 := by
  apply le_antisymm
  · rw [sup_le_iff]
    exact ⟨fiveC_le_fiveG4, Subgroup.zpowers_le.mpr fiveZG.2⟩
  · rw [fiveG4, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact fiveT1_mem_sup
    · rw [show fiveT2 = fiveT1 * fiveBeta by
        rw [fiveBeta, ← mul_assoc, fiveT1_sq, one_mul]]
      exact Subgroup.mul_mem _ fiveT1_mem_sup (Subgroup.mem_sup_left fiveBeta_mem_C)
    · rw [show fiveT3 = fiveT1 * fiveAlpha by
        rw [fiveAlpha, ← mul_assoc, fiveT1_sq, one_mul]]
      exact Subgroup.mul_mem _ fiveT1_mem_sup (Subgroup.mem_sup_left fiveAlpha_mem_C)

private theorem fiveZ_not_mem_C : fiveZ ∉ fiveC := by
  intro hzC
  have hdet1 : Matrix.GeneralLinearGroup.det fiveZ = 1 := by
    have hle : fiveC ≤
        (Matrix.GeneralLinearGroup.det : GL (Fin 4) (ZMod 5) →* (ZMod 5)ˣ).ker := by
      rw [fiveC, Subgroup.closure_le]
      intro x hx
      have hx' : Matrix.GeneralLinearGroup.det x = 1 := by
        rcases hx with rfl | rfl
        · rw [fiveAlpha, map_mul]
          have h1 : Matrix.GeneralLinearGroup.det fiveT1 = -1 := by
            apply Units.ext
            rw [Matrix.GeneralLinearGroup.val_det_apply, fiveT1_coe]
            decide
          have h3 : Matrix.GeneralLinearGroup.det fiveT3 = -1 := by
            apply Units.ext
            rw [Matrix.GeneralLinearGroup.val_det_apply, fiveT3_coe]
            decide
          rw [h1, h3]; decide
        · rw [fiveBeta, map_mul]
          have h1 : Matrix.GeneralLinearGroup.det fiveT1 = -1 := by
            apply Units.ext
            rw [Matrix.GeneralLinearGroup.val_det_apply, fiveT1_coe]
            decide
          have h2 : Matrix.GeneralLinearGroup.det fiveT2 = -1 := by
            apply Units.ext
            rw [Matrix.GeneralLinearGroup.val_det_apply, fiveT2_coe]
            decide
          rw [h1, h2]; decide
      simpa [MonoidHom.mem_ker] using hx'
    exact hle hzC
  rw [fiveZ_det] at hdet1
  have h : (-1 : ZMod 5) = 1 := by
    have := congrArg Units.val hdet1
    simpa using this
  exact (by decide : (-1 : ZMod 5) ≠ 1) h

private theorem fiveC_inf_fiveZ : fiveC ⊓ Subgroup.zpowers fiveZ = ⊥ := by
  have hcard : Nat.card ↥(Subgroup.zpowers fiveZ) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact fiveZ_sq) fiveZ_ne_one]
  have hprime : (Nat.card ↥(Subgroup.zpowers fiveZ)).Prime := by
    rw [hcard]; norm_num
  have hsub : (fiveC ⊓ Subgroup.zpowers fiveZ).subgroupOf (Subgroup.zpowers fiveZ) = ⊥ := by
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card
      (hp := ⟨hprime⟩) (H := (fiveC ⊓ Subgroup.zpowers fiveZ).subgroupOf
        (Subgroup.zpowers fiveZ)) with h | h
    · exact h
    · exfalso
      have hzmem : (⟨fiveZ, Subgroup.mem_zpowers fiveZ⟩ : ↥(Subgroup.zpowers fiveZ)) ∈
          (fiveC ⊓ Subgroup.zpowers fiveZ).subgroupOf (Subgroup.zpowers fiveZ) := by
        rw [h]; exact Subgroup.mem_top _
      exact fiveZ_not_mem_C (by simpa using (Subgroup.mem_subgroupOf.mp hzmem))
  have hsub' : (fiveC ⊓ Subgroup.zpowers fiveZ).subgroupOf (Subgroup.zpowers fiveZ) =
      (⊥ : Subgroup (GL (Fin 4) (ZMod 5))).subgroupOf (Subgroup.zpowers fiveZ) := by
    rw [hsub, Subgroup.bot_subgroupOf]
  have hinf := Subgroup.subgroupOf_inj.mp hsub'
  simpa using hinf

private noncomputable def fiveEA5 :
    PG 2 a5Rels ≃* alternatingGroup (Fin 5) :=
  a5Equiv (C := alternatingGroup (Fin 5)) (a := pa) (b := pb)
    (by simpa using pa_sq)
    (by rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]; exact pb_cube)
    papb_pow_five closure_pa_pb
    (by rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num)

private noncomputable def fiveA5Hom :
    PG 2 a5Rels →* GL (Fin 4) (ZMod 5) :=
  a5Hom fiveAlpha_sq fiveBeta_cube fiveAlphaBeta_pow_five

private theorem fiveA5Hom_range : fiveA5Hom.range = fiveC := by
  rw [fiveA5Hom, range_a5Hom, fiveC]

private theorem fiveA5Hom_beta :
    fiveA5Hom (PresentedGroup.of 1) = fiveBeta := by
  rw [fiveA5Hom, a5Hom_of]
  rfl

private theorem fiveA5Hom_injective :
    Function.Injective fiveA5Hom := by
  have hA5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hPG : IsSimpleGroup (PG 2 a5Rels) :=
    @MulEquiv.isSimpleGroup _ _ _ _ hA5 fiveEA5
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hPG fiveA5Hom.ker
    (MonoidHom.normal_ker fiveA5Hom) with h | h
  · exact h
  · exfalso
    have hbker : fiveA5Hom (PresentedGroup.of 1) = 1 := by
      rw [← MonoidHom.mem_ker, h]
      exact Subgroup.mem_top _
    rw [fiveA5Hom_beta] at hbker
    exact fiveBeta_ne_one hbker

private noncomputable def fiveCA5Equiv :
    fiveC ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.subgroupCongr fiveA5Hom_range.symm).trans
    ((MonoidHom.ofInjective fiveA5Hom_injective).symm.trans fiveEA5)

private noncomputable def fiveC4 : Subgroup fiveG4 := fiveC.subgroupOf fiveG4

private noncomputable def fiveZ4 : Subgroup fiveG4 := Subgroup.zpowers fiveZG

private theorem fiveZ4_eq : fiveZ4 = (Subgroup.zpowers fiveZ).subgroupOf fiveG4 := by
  ext x
  rw [fiveZ4, Subgroup.mem_zpowers_iff, Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩

private theorem fiveC4_sup_fiveZ4 : fiveC4 ⊔ fiveZ4 = ⊤ := by
  rw [fiveC4, fiveZ4_eq,
    ← Subgroup.subgroupOf_sup (A' := Subgroup.zpowers fiveZ) fiveC_le_fiveG4
      (Subgroup.zpowers_le.mpr fiveZG.2)]
  rw [fiveC_sup_fiveZ, Subgroup.subgroupOf_self]

private theorem fiveC4_inf_fiveZ4 : fiveC4 ⊓ fiveZ4 = ⊥ := by
  rw [fiveC4, fiveZ4_eq]
  rw [show fiveC.subgroupOf fiveG4 ⊓ (Subgroup.zpowers fiveZ).subgroupOf fiveG4 =
      (fiveC ⊓ Subgroup.zpowers fiveZ).subgroupOf fiveG4 by
    ext x
    simp [Subgroup.mem_subgroupOf]]
  rw [fiveC_inf_fiveZ, Subgroup.bot_subgroupOf]

private instance fiveZ4_normal : fiveZ4.Normal :=
  Subgroup.normal_of_le_center (by
    rw [fiveZ4]
    exact Subgroup.zpowers_le.mpr fiveZ_center)

private theorem fiveIsComplement_C4_Z4 : Subgroup.IsComplement' fiveC4 fiveZ4 := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff, fiveC4_inf_fiveZ4]
  · rw [← Subgroup.mul_normal fiveC4 fiveZ4, fiveC4_sup_fiveZ4, Subgroup.coe_top]

private noncomputable def fiveQuotEquivA5 :
    fiveG4 ⧸ fiveZ4 ≃* alternatingGroup (Fin 5) :=
  (Subgroup.IsComplement'.QuotientMulEquiv fiveIsComplement_C4_Z4).trans
    ((Subgroup.subgroupOfEquivOfLe fiveC_le_fiveG4).trans fiveCA5Equiv)

private theorem fiveCenter_eq : Subgroup.center fiveG4 = fiveZ4 := by
  have hA5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimple : IsSimpleGroup (fiveG4 ⧸ fiveZ4) := MulEquiv.isSimpleGroup fiveQuotEquivA5
  have hnc : ¬ IsMulCommutative (fiveG4 ⧸ fiveZ4) := by
    intro h
    have hA5 : IsMulCommutative (alternatingGroup (Fin 5)) :=
      Function.Surjective.isMulCommutative fiveQuotEquivA5.surjective h
    rw [alternatingGroup.isMulCommutative_iff_card_le_three] at hA5
    simp at hA5
  exact le_antisymm (center_le_of_quotient_simple fiveZ4 hsimple hnc)
    (Subgroup.zpowers_le.mpr fiveZ_center)

private theorem fiveZG_sq : fiveZG * fiveZG = 1 := by
  apply Subtype.ext
  simpa [fiveZG] using fiveZ_sq

private theorem fiveZG_ne_one : fiveZG ≠ 1 := by
  intro h
  have := congrArg (fun g : fiveG4 => (g : GL (Fin 4) (ZMod 5))) h
  exact fiveZ_ne_one (by simpa [fiveZG] using this)

private theorem fiveCenter_card :
    Nat.card ↥(Subgroup.center fiveG4) ∣ 2 := by
  rw [fiveCenter_eq, fiveZ4, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact fiveZG_sq) fiveZG_ne_one]

private theorem fiveIsPSL_quotient :
    IsL2OrSz (fiveG4 ⧸ Subgroup.center fiveG4) 2 := by
  have h : IsPSL 2 2 2 (fiveG4 ⧸ Subgroup.center fiveG4) := by
    refine CFSG.Quasithin.H13.OddSyl.isPSL_two_two_two_of_alt_five ?_
    exact (QuotientGroup.quotientMulEquivOfEq fiveCenter_eq).trans fiveQuotEquivA5
  exact Or.inl h

variable {f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5)}

private def fiveW (F : OrthFrameFive f) : Fin 4 → (Fin 4 → ZMod 5) :=
  ![F.a, F.a + F.a + F.s + F.s' + F.s' + F.s',
    F.s + F.s' + F.s' + F.s' + F.s', F.b]

private lemma fiveW_gram (F : OrthFrameFive f) (i j : Fin 4) :
    f (fiveW F i) (fiveW F j) = fiveGram4 i j := by
  have hs's : f F.s' F.s = 1 := by rw [F.symm F.s' F.s, F.pair]
  have hsa : f F.s F.a = 0 := by rw [F.symm F.s F.a, F.a_orth_s]
  have hs'a : f F.s' F.a = 0 := by rw [F.symm F.s' F.a, F.a_orth_s']
  have hbs : f F.b F.s = 0 := F.b_orth_s
  have hsb : f F.s F.b = 0 := by rw [F.symm F.s F.b, F.b_orth_s]
  have hbs' : f F.b F.s' = 0 := F.b_orth_s'
  have hs'b : f F.s' F.b = 0 := by rw [F.symm F.s' F.b, F.b_orth_s']
  have hba : f F.b F.a = 0 := F.b_orth_a
  have hab : f F.a F.b = 0 := by rw [F.symm F.a F.b, F.b_orth_a]
  fin_cases i <;> fin_cases j <;>
    simp [fiveW, fiveGram4, F.norm_a, F.norm_b, F.isotropic_s, F.isotropic_s', F.pair, hs's,
      F.a_orth_s, F.a_orth_s', hsa, hs'a, hbs, hsb, hbs', hs'b, hba, hab,
      map_add, LinearMap.add_apply] <;>
    decide

private lemma fiveW_linearIndependent (F : OrthFrameFive f) :
    LinearIndependent (ZMod 5) (fiveW F) := by
  refine CFSG.StandardType.linearIndependent_of_det_ne_zero (fiveW F)
    (fun i => f.flip (fiveW F i)) ?_
  rw [show (Matrix.of fun i j => (f.flip (fiveW F i)) (fiveW F j)) = fiveGram4.transpose by
    ext i j
    rw [Matrix.transpose_apply, Matrix.of_apply, LinearMap.BilinForm.flip_apply, fiveW_gram]]
  rw [show fiveGram4.transpose = fiveGram4 by decide]
  decide

private def fiveP (F : OrthFrameFive f) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  Matrix.of fun i j => fiveW F j i

private lemma fiveP_isUnit (F : OrthFrameFive f) : IsUnit (fiveP F) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have hcol : (fiveP F).col = fiveW F := by
    funext j i
    rfl
  rw [hcol]
  exact fiveW_linearIndependent F

private noncomputable def fivePGL (F : OrthFrameFive f) : GL (Fin 4) (ZMod 5) :=
  (fiveP_isUnit F).unit

private theorem fivePGL_coe (F : OrthFrameFive f) :
    (fivePGL F : Matrix (Fin 4) (Fin 4) (ZMod 5)) = fiveP F :=
  IsUnit.unit_spec _

private lemma fiveTM_mulVec (i : Fin 3) (j : Fin 4) :
    fiveTM i *ᵥ Pi.single j 1 =
      Pi.single j (1 : ZMod 5) +
        fiveGram4 j (Fin.castSucc i) • Pi.single (Fin.castSucc i) (1 : ZMod 5) := by
  fin_cases i <;> fin_cases j <;>
    ext k <;> fin_cases k <;>
    simp [fiveTM, fiveGram4, Matrix.mulVec, dotProduct, Pi.single_apply] <;>
    decide

private lemma fiveP_mulVec_single (F : OrthFrameFive f) (j : Fin 4) :
    fiveP F *ᵥ Pi.single j 1 = fiveW F j := by
  rw [Matrix.mulVec_single_one]
  ext i
  rfl

private lemma fiveOrthRefl_mul_fiveP (F : OrthFrameFive f) (i : Fin 3) :
    (orthRefl f (fiveW F (Fin.castSucc i)) :
        Matrix (Fin 4) (Fin 4) (ZMod 5)) * fiveP F = fiveP F * fiveTM i := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [fiveP_mulVec_single, fiveTM_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    fiveP_mulVec_single, fiveP_mulVec_single]
  rw [orthRefl_mulVec f (by rw [fiveW_gram]; fin_cases i <;> decide)]
  rw [fiveW_gram]

private lemma fiveConj_orthRefl (F : OrthFrameFive f) (i : Fin 3) :
    MulAut.conj (fivePGL F)⁻¹ (orthRefl f (fiveW F (Fin.castSucc i))) = fiveTMGL i := by
  rw [MulAut.conj_apply, inv_inv]
  have hGL : orthRefl f (fiveW F (Fin.castSucc i)) * fivePGL F = fivePGL F * fiveTMGL i := by
    apply Units.ext
    simpa [Units.val_mul, fivePGL_coe, fiveTMGL_coe] using fiveOrthRefl_mul_fiveP F i
  calc (fivePGL F)⁻¹ * orthRefl f (fiveW F (Fin.castSucc i)) * fivePGL F
      = (fivePGL F)⁻¹ * (orthRefl f (fiveW F (Fin.castSucc i)) * fivePGL F) := by group
    _ = (fivePGL F)⁻¹ * (fivePGL F * fiveTMGL i) := by rw [hGL]
    _ = fiveTMGL i := by rw [← mul_assoc, inv_mul_cancel, one_mul]

private noncomputable def fiveL1 (F : OrthFrameFive f) : Subgroup (GL (Fin 4) (ZMod 5)) :=
  Subgroup.closure {orthRefl f (fiveW F 0), orthRefl f (fiveW F 1), orthRefl f (fiveW F 2)}

private lemma fiveL1_map_conj (F : OrthFrameFive f) :
    (fiveL1 F).map (MulAut.conj (fivePGL F)⁻¹).toMonoidHom = fiveG4 := by
  rw [fiveL1, fiveG4, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl | rfl, rfl⟩
    · exact Or.inl (fiveConj_orthRefl F 0)
    · exact Or.inr (Or.inl (fiveConj_orthRefl F 1))
    · exact Or.inr (Or.inr (fiveConj_orthRefl F 2))
  · rintro (rfl | rfl | rfl)
    · exact ⟨orthRefl f (fiveW F 0), Or.inl rfl, fiveConj_orthRefl F 0⟩
    · exact ⟨orthRefl f (fiveW F 1), Or.inr (Or.inl rfl), fiveConj_orthRefl F 1⟩
    · exact ⟨orthRefl f (fiveW F 2), Or.inr (Or.inr rfl), fiveConj_orthRefl F 2⟩

theorem radicalOutcome_of_isReflModel_five {L : Type} [Group L]
    {D : Set L} {t : L} (ht : t ∈ D)
    {f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5)} (hsymm : ∀ x y, f x y = f y x)
    (hnd : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hwitt : ∀ a b : Fin 4 → ZMod 5, f a a = 0 → f a b = 0 → f b b = 0 →
      ∃ c d : ZMod 5, (c ≠ 0 ∨ d ≠ 0) ∧ c • a + d • b = 0)
    (h : IsReflModel 5 4 f L D) : RadicalOutcome L t := by
  classical
  obtain ⟨e, he⟩ := h
  obtain ⟨v, hv, hrv⟩ := exists_eq_orthRefl_of_mem f (he t ht)
  obtain ⟨F, hFa⟩ := exists_orthFrameFive f hsymm hnd hwitt hv
  let R : Subgroup (GL (Fin 4) (ZMod 5)) := Subgroup.closure (orthReflSet 5 4 f)
  set L1 : Subgroup (GL (Fin 4) (ZMod 5)) := fiveL1 F with hL1
  have hL1R : L1 ≤ R := by
    rw [hL1, fiveL1, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.subset_closure (orthRefl_mem f (v := fiveW F 0) (by rw [fiveW_gram]; decide))
    · exact Subgroup.subset_closure (orthRefl_mem f (v := fiveW F 1) (by rw [fiveW_gram]; decide))
    · exact Subgroup.subset_closure (orthRefl_mem f (v := fiveW F 2) (by rw [fiveW_gram]; decide))
  have hw1 : fiveW F 0 = v := by
    simp [fiveW, hFa]
  have het1 : e t = ⟨orthRefl f (fiveW F 0),
      Subgroup.subset_closure
        (orthRefl_mem f (v := fiveW F 0) (by rw [fiveW_gram]; decide))⟩ := by
    apply Subtype.ext
    change (e t : GL (Fin 4) (ZMod 5)) = orthRefl f (fiveW F 0)
    rw [hw1, hrv]
  have hetH : e t ∈ L1.subgroupOf R := by
    rw [Subgroup.mem_subgroupOf, het1]
    exact Subgroup.subset_closure (by simp)
  have hG4 : RadicalOutcome fiveG4 fiveT1G := by
    refine RadicalOutcome.of_top fiveNormalClosure_top fiveCenter_card (n := 2) (by norm_num) ?_
    exact fiveIsPSL_quotient
  let eL1G4 : L1 ≃* fiveG4 :=
    (MulEquiv.subgroupMap (MulAut.conj (fivePGL F)⁻¹) L1).trans
      (MulEquiv.subgroupCongr (fiveL1_map_conj F))
  have heL1 : eL1G4 ⟨orthRefl f (fiveW F 0), by
      exact Subgroup.subset_closure (by simp)⟩ = fiveT1G := by
    apply Subtype.ext
    change MulAut.conj (fivePGL F)⁻¹ (orthRefl f (fiveW F 0)) = fiveT1
    rw [show fiveT1 = fiveTMGL 0 from fiveTMGL_zero.symm]
    exact fiveConj_orthRefl F 0
  have hL1outcome : RadicalOutcome L1 ⟨orthRefl f (fiveW F 0), by
      exact Subgroup.subset_closure (by simp)⟩ := by
    refine RadicalOutcome.of_mulEquiv eL1G4 ?_
    rw [heL1]
    exact hG4
  have hHoutcome : RadicalOutcome ↥(L1.subgroupOf R) ⟨e t, hetH⟩ := by
    refine RadicalOutcome.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL1R) ?_
    have hx : (Subgroup.subgroupOfEquivOfLe hL1R) ⟨e t, hetH⟩ =
        ⟨orthRefl f (fiveW F 0), by
          exact Subgroup.subset_closure (by simp)⟩ := by
      apply Subtype.ext
      simp [Subgroup.subgroupOfEquivOfLe_apply_coe, het1]
    rw [hx]
    exact hL1outcome
  have hRoutcome : RadicalOutcome R (e t) := RadicalOutcome.of_le hetH hHoutcome
  exact RadicalOutcome.of_mulEquiv e hRoutcome

end CFSG.LocalAnalysis.WeakClosure81.CoreRadical

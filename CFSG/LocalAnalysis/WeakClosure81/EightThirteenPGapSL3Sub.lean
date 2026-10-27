module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapSl2Emb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
open Matrix

section Corner

variable {F : Type} [Field F]

private def wcgapsb_blkMat (g : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![g 0 0, 0, g 0 1; 0, 1, 0; g 1 0, 0, g 1 1]

private theorem wcgapsb_blkMat_mul (g h : Matrix (Fin 2) (Fin 2) F) :
    wcgapsb_blkMat (g * h) = wcgapsb_blkMat g * wcgapsb_blkMat h := by
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [wcgapsb_blkMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

private theorem wcgapsb_blkMat_one : wcgapsb_blkMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [wcgapsb_blkMat]

private theorem wcgapsb_det_blkMat (g : Matrix (Fin 2) (Fin 2) F) :
    (wcgapsb_blkMat g).det = g.det := by
  simp [wcgapsb_blkMat, Matrix.det_fin_three, Matrix.det_fin_two]

private def wcgapsb_cornerHom : Matrix.SpecialLinearGroup (Fin 2) F →*
    Matrix.SpecialLinearGroup (Fin 3) F where
  toFun g := ⟨wcgapsb_blkMat (g : Matrix (Fin 2) (Fin 2) F), by
    rw [wcgapsb_det_blkMat]; exact g.2⟩
  map_one' := Subtype.ext (by simp [wcgapsb_blkMat_one])
  map_mul' g h := Subtype.ext (by
    change wcgapsb_blkMat ((g * h : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) =
      wcgapsb_blkMat (g : Matrix (Fin 2) (Fin 2) F) *
        wcgapsb_blkMat (h : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.coe_mul, wcgapsb_blkMat_mul])

private theorem wcgapsb_cornerHom_coe (g : Matrix.SpecialLinearGroup (Fin 2) F) :
    ((wcgapsb_cornerHom g : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = wcgapsb_blkMat (g : Matrix (Fin 2) (Fin 2) F) := rfl

private theorem wcgapsb_blkMat_injective : Function.Injective (wcgapsb_blkMat (F := F)) := by
  intro g h hgh
  ext a b
  fin_cases a <;> fin_cases b
  · exact congrFun (congrFun hgh 0) 0
  · exact congrFun (congrFun hgh 0) 2
  · exact congrFun (congrFun hgh 2) 0
  · exact congrFun (congrFun hgh 2) 2

private theorem wcgapsb_cornerHom_injective :
    Function.Injective (wcgapsb_cornerHom (F := F)) := by
  intro g h hgh
  apply Subtype.ext
  apply wcgapsb_blkMat_injective (F := F)
  rw [← wcgapsb_cornerHom_coe g, ← wcgapsb_cornerHom_coe h]
  exact congrArg (fun A : Matrix.SpecialLinearGroup (Fin 3) F =>
    (A : Matrix (Fin 3) (Fin 3) F)) hgh

private def wcgapsb_e12 (c : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two]⟩

private theorem wcgapsb_e12_mem (c : F) : wcgapsb_e12 c ∈ unitriangular 2 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F) i j = 0
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp
  · change (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F) i i = 1
    fin_cases i <;> simp

private theorem wcgapsb_blkMat_e12 (c : F) :
    wcgapsb_blkMat (!![1, c; 0, 1] : Matrix (Fin 2) (Fin 2) F) = wM c := by
  ext a b; fin_cases a <;> fin_cases b <;> simp [wcgapsb_blkMat, wM]

private theorem wcgapsb_e12_corner (c : F) :
    wcgapsb_cornerHom (wcgapsb_e12 c) = wMat c := by
  apply Subtype.ext
  rw [wcgapsb_cornerHom_coe]
  simpa only [wcgapsb_e12, coe_wMat] using wcgapsb_blkMat_e12 c

private theorem wcgapsb_unitri_entries {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ unitriangular 3 F) :
    A 0 0 = 1 ∧ A 1 1 = 1 ∧ A 2 2 = 1 ∧ A 1 0 = 0 ∧ A 2 0 = 0 ∧ A 2 1 = 0 :=
  ⟨hA.2 0, hA.2 1, hA.2 2, hA.1 1 0 (by decide), hA.1 2 0 (by decide),
    hA.1 2 1 (by decide)⟩

private theorem wcgapsb_blkMat_unitri (u : Matrix.SpecialLinearGroup (Fin 2) F)
    (hu : u ∈ unitriangular 2 F) :
    wcgapsb_blkMat (u : Matrix (Fin 2) (Fin 2) F) = wM (u 0 1) := by
  have h10 : (u : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hu.1 1 0 (by decide)
  have h00 : (u : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := hu.2 0
  have h11 : (u : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := hu.2 1
  ext a b; fin_cases a <;> fin_cases b <;>
    simp [wcgapsb_blkMat, wM, h10, h00, h11]

private theorem wcgapsb_cornerHom_eq_wMat (u : Matrix.SpecialLinearGroup (Fin 2) F)
    (hu : u ∈ unitriangular 2 F) : wcgapsb_cornerHom u = wMat (u 0 1) := by
  apply Subtype.ext
  rw [wcgapsb_cornerHom_coe]
  exact wcgapsb_blkMat_unitri u hu

private theorem wcgapsb_xMat_mem_unitriangular (a : F) : xMat a ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change xM a i j = 0
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [xM]
  · change xM a i i = 1
    fin_cases i <;> simp [xM]

private theorem wcgapsb_yMat_mem_unitriangular (b : F) : yMat b ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change yM b i j = 0
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [yM]
  · change yM b i i = 1
    fin_cases i <;> simp [yM]

private theorem wcgapsb_wMat_mem_unitriangular (c : F) : wMat c ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change wM c i j = 0
    fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [wM]
  · change wM c i i = 1
    fin_cases i <;> simp [wM]

private theorem wcgapsb_wMat_mem_centralizer (c : F) :
    wMat c ∈ centralizer (unitriangular 3 F :
      Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  rw [Subgroup.mem_centralizer_iff]
  intro A hA
  obtain ⟨h00, h11, h22, h10, h20, h21⟩ := wcgapsb_unitri_entries hA
  apply Subtype.ext
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [wMat, wM, coe_wMat, Matrix.mul_apply, Fin.sum_univ_three, h00, h11, h22, h10, h20,
      h21]
  all_goals ring

private theorem wcgapsb_mem_inf_center_entries {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ unitriangular 3 F ⊓ centralizer (unitriangular 3 F :
      Set (Matrix.SpecialLinearGroup (Fin 3) F))) :
    A 0 1 = 0 ∧ A 1 2 = 0 := by
  obtain ⟨-, hAC⟩ := Subgroup.mem_inf.mp hA
  have hx := Subgroup.mem_centralizer_iff.mp hAC (xMat 1) (wcgapsb_xMat_mem_unitriangular 1)
  have hy := Subgroup.mem_centralizer_iff.mp hAC (yMat 1) (wcgapsb_yMat_mem_unitriangular 1)
  have h12 : A 1 2 = 0 := by
    have h := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) F =>
      (B : Matrix (Fin 3) (Fin 3) F) 0 2) hx
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    simp [xMat, xM, Matrix.mul_apply, Fin.sum_univ_three] at h
    linear_combination h
  have h01 : A 0 1 = 0 := by
    have h := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 3) F =>
      (B : Matrix (Fin 3) (Fin 3) F) 0 2) hy
    simp only [Matrix.SpecialLinearGroup.coe_mul] at h
    simp [yMat, yM, Matrix.mul_apply, Fin.sum_univ_three] at h
    linear_combination h
  exact ⟨h01, h12⟩

private theorem wcgapsb_mem_inf_center_eq_wMat {A : Matrix.SpecialLinearGroup (Fin 3) F}
    (hA : A ∈ unitriangular 3 F ⊓ centralizer (unitriangular 3 F :
      Set (Matrix.SpecialLinearGroup (Fin 3) F))) :
    A = wMat (A 0 2) := by
  obtain ⟨h01, h12⟩ := wcgapsb_mem_inf_center_entries hA
  obtain ⟨h00, h11, h22, h10, h20, h21⟩ := wcgapsb_unitri_entries (Subgroup.mem_inf.mp hA).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wMat, wM, h01, h12, h00, h11, h22, h10, h20, h21]

private theorem wcgapsb_inf_centralizer_eq_map :
    (unitriangular 3 F ⊓ centralizer (unitriangular 3 F :
      Set (Matrix.SpecialLinearGroup (Fin 3) F))) =
      (unitriangular 2 F).map (wcgapsb_cornerHom (F := F)) := by
  apply le_antisymm
  · rintro A hA
    rw [wcgapsb_mem_inf_center_eq_wMat hA]
    exact Subgroup.mem_map.mpr ⟨wcgapsb_e12 (A 0 2), wcgapsb_e12_mem (A 0 2),
      wcgapsb_e12_corner (A 0 2)⟩
  · rintro A ⟨u, hu, rfl⟩
    rw [wcgapsb_cornerHom_eq_wMat u hu]
    exact Subgroup.mem_inf.mpr ⟨wcgapsb_wMat_mem_unitriangular (u 0 1),
      wcgapsb_wMat_mem_centralizer (u 0 1)⟩

private theorem wcgapsb_slTwoDiag_mem_normalizer (l : Fˣ) :
    wcgapsb_cornerHom (slTwoDiag l) ∈ normalizer (unitriangular 3 F :
      Set (Matrix.SpecialLinearGroup (Fin 3) F)) := by
  rw [normalizer_unitriangular]
  refine mem_upperTriangular.mpr ?_
  intro i j hij
  change (wcgapsb_cornerHom (slTwoDiag l) : Matrix (Fin 3) (Fin 3) F) i j = 0
  rw [wcgapsb_cornerHom_coe]
  fin_cases i <;> fin_cases j <;>
    first | exact absurd hij (by decide) | simp [wcgapsb_blkMat, slTwoDiag]

end Corner

theorem centralKData_slThree_unitriangular {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = 4) :
    CentralKData (unitriangular 3 F : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
      (unitriangular 3 F ⊓ centralizer
        ((unitriangular 3 F : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
          Set (Matrix.SpecialLinearGroup (Fin 3) F))) := by
  have hUcard : Nat.card (unitriangular 3 F) = 64 := by
    rw [card_unitriangular (K := F) 3, hF]
    norm_num
  have hS : IsPGroup 2 (unitriangular 3 F :
      Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :=
    IsPGroup.of_card (n := 6) (by rw [hUcard]; norm_num)
  exact centralKData_of_sl2_embedding
    (S := (unitriangular 3 F : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)))
    (A := (unitriangular 3 F ⊓ centralizer ((unitriangular 3 F :
      Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) :
        Set (Matrix.SpecialLinearGroup (Fin 3) F))))
    hS inf_le_left hF (wcgapsb_cornerHom (F := F)) (wcgapsb_cornerHom_injective (F := F))
    (wcgapsb_inf_centralizer_eq_map (F := F)) (wcgapsb_slTwoDiag_mem_normalizer (F := F))

end CFSG.LocalAnalysis.WeakClosure81

end

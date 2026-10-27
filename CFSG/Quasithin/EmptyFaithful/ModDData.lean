module

public import CFSG.Quasithin.Recognition.CertU33PresInputs

public section

namespace CFSG.Quasithin.ModD

open CFSG.CosetTable CFSG.Quasithin

@[expose] def vImg : Fin 5 → Equiv.Perm (Fin 63)
  | 0 => List.formPerm [1, 61, 36, 25] *
      List.formPerm [2, 8] *
      List.formPerm [3, 53, 38, 17] *
      List.formPerm [4, 33, 13, 39] *
      List.formPerm [5, 27, 42, 49] *
      List.formPerm [6, 41, 11, 31] *
      List.formPerm [7, 19, 40, 57] *
      List.formPerm [9, 59, 44, 23] *
      List.formPerm [10, 51, 46, 15] *
      List.formPerm [12, 29, 34, 47] *
      List.formPerm [14, 21, 32, 55] *
      List.formPerm [16, 52] *
      List.formPerm [18, 60] *
      List.formPerm [20, 22, 30, 28] *
      List.formPerm [24, 54] *
      List.formPerm [26, 62] *
      List.formPerm [37, 43] *
      List.formPerm [48, 50, 58, 56]
  | 1 => List.formPerm [1, 40, 3, 42] *
      List.formPerm [4, 11] *
      List.formPerm [5, 36, 7, 38] *
      List.formPerm [6, 13] *
      List.formPerm [9, 32, 10, 34] *
      List.formPerm [12, 44, 14, 46] *
      List.formPerm [15, 29, 23, 21] *
      List.formPerm [16, 54, 26, 60] *
      List.formPerm [17, 27, 25, 19] *
      List.formPerm [18, 52, 24, 62] *
      List.formPerm [20, 58, 30, 48] *
      List.formPerm [22, 56, 28, 50] *
      List.formPerm [31, 33] *
      List.formPerm [35, 45] *
      List.formPerm [37, 43] *
      List.formPerm [39, 41] *
      List.formPerm [47, 59, 55, 51] *
      List.formPerm [49, 61, 57, 53]
  | 2 => List.formPerm [1, 38] *
      List.formPerm [2, 35] *
      List.formPerm [4, 24] *
      List.formPerm [5, 61] *
      List.formPerm [6, 60] *
      List.formPerm [7, 25] *
      List.formPerm [8, 45] *
      List.formPerm [10, 44] *
      List.formPerm [11, 54] *
      List.formPerm [12, 15] *
      List.formPerm [13, 18] *
      List.formPerm [14, 51] *
      List.formPerm [16, 41] *
      List.formPerm [17, 40] *
      List.formPerm [20, 50] *
      List.formPerm [21, 47] *
      List.formPerm [23, 34] *
      List.formPerm [26, 31] *
      List.formPerm [27, 57] *
      List.formPerm [30, 56] *
      List.formPerm [32, 59] *
      List.formPerm [33, 62] *
      List.formPerm [39, 52] *
      List.formPerm [42, 53]
  | 3 => List.formPerm [1, 61, 42] *
      List.formPerm [2, 35, 43] *
      List.formPerm [3, 25, 7] *
      List.formPerm [4, 24, 28] *
      List.formPerm [5, 38, 53] *
      List.formPerm [6, 60, 48] *
      List.formPerm [8, 45, 37] *
      List.formPerm [9, 15, 12] *
      List.formPerm [10, 51, 32] *
      List.formPerm [11, 54, 58] *
      List.formPerm [13, 18, 22] *
      List.formPerm [14, 44, 59] *
      List.formPerm [16, 50, 33] *
      List.formPerm [17, 40, 36] *
      List.formPerm [20, 41, 62] *
      List.formPerm [21, 47, 55] *
      List.formPerm [23, 34, 46] *
      List.formPerm [26, 56, 39] *
      List.formPerm [27, 57, 49] *
      List.formPerm [30, 31, 52]
  | 4 => List.formPerm [0, 43, 37] *
      List.formPerm [1, 31, 32] *
      List.formPerm [2, 50, 48] *
      List.formPerm [3, 18, 15] *
      List.formPerm [4, 23, 27] *
      List.formPerm [5, 55, 60] *
      List.formPerm [6, 42, 44] *
      List.formPerm [7, 10, 11] *
      List.formPerm [8, 30, 22] *
      List.formPerm [9, 62, 53] *
      List.formPerm [12, 38, 41] *
      List.formPerm [13, 51, 57] *
      List.formPerm [14, 19, 26] *
      List.formPerm [16, 34, 49] *
      List.formPerm [17, 47, 33] *
      List.formPerm [20, 58, 45] *
      List.formPerm [21, 39, 61] *
      List.formPerm [24, 59, 36] *
      List.formPerm [25, 46, 52] *
      List.formPerm [28, 35, 56] *
      List.formPerm [29, 54, 40]

@[expose] def lImg : Fin 5 → Equiv.Perm (Fin 63)
  | 0 => List.formPerm [1, 28, 40, 54] *
      List.formPerm [2, 18, 37, 30] *
      List.formPerm [3, 33, 59, 53] *
      List.formPerm [5, 16, 6, 10] *
      List.formPerm [7, 24, 56, 42] *
      List.formPerm [8, 17, 32, 29] *
      List.formPerm [9, 38, 47, 41] *
      List.formPerm [11, 27, 35, 20] *
      List.formPerm [12, 23, 34, 14] *
      List.formPerm [13, 26, 61, 58] *
      List.formPerm [15, 36, 48, 43] *
      List.formPerm [19, 22, 45, 50] *
      List.formPerm [21, 31, 60, 51] *
      List.formPerm [46, 49, 62, 57]
  | 1 => List.formPerm [1, 60, 7, 48] *
      List.formPerm [2, 27, 8, 23] *
      List.formPerm [3, 45, 9, 61] *
      List.formPerm [11, 29, 12, 30] *
      List.formPerm [13, 59, 19, 47] *
      List.formPerm [14, 37, 20, 32] *
      List.formPerm [15, 40, 21, 56] *
      List.formPerm [17, 34, 18, 35] *
      List.formPerm [22, 41, 26, 53] *
      List.formPerm [24, 43, 28, 51] *
      List.formPerm [31, 42, 36, 54] *
      List.formPerm [33, 50, 38, 58] *
      List.formPerm [39, 52, 55, 44] *
      List.formPerm [46, 57, 62, 49]
  | 2 => List.formPerm [1, 32] *
      List.formPerm [2, 56] *
      List.formPerm [3, 47] *
      List.formPerm [4, 25] *
      List.formPerm [5, 55] *
      List.formPerm [6, 39] *
      List.formPerm [7, 8] *
      List.formPerm [10, 52] *
      List.formPerm [11, 31] *
      List.formPerm [12, 51] *
      List.formPerm [13, 33] *
      List.formPerm [14, 28] *
      List.formPerm [15, 18] *
      List.formPerm [16, 44] *
      List.formPerm [17, 48] *
      List.formPerm [19, 53] *
      List.formPerm [20, 54] *
      List.formPerm [21, 30] *
      List.formPerm [23, 24] *
      List.formPerm [26, 50] *
      List.formPerm [27, 42] *
      List.formPerm [29, 60] *
      List.formPerm [34, 43] *
      List.formPerm [35, 36] *
      List.formPerm [37, 40] *
      List.formPerm [38, 61] *
      List.formPerm [41, 45] *
      List.formPerm [46, 62]
  | 3 => List.formPerm [0, 4, 25] *
      List.formPerm [1, 33, 23] *
      List.formPerm [2, 28, 61] *
      List.formPerm [3, 18, 48] *
      List.formPerm [5, 39, 62] *
      List.formPerm [6, 55, 46] *
      List.formPerm [7, 53, 20] *
      List.formPerm [8, 54, 19] *
      List.formPerm [9, 30, 21] *
      List.formPerm [10, 52, 57] *
      List.formPerm [11, 31, 22] *
      List.formPerm [12, 51, 58] *
      List.formPerm [13, 32, 24] *
      List.formPerm [14, 56, 38] *
      List.formPerm [15, 47, 17] *
      List.formPerm [16, 44, 49] *
      List.formPerm [26, 35, 43] *
      List.formPerm [27, 40, 41] *
      List.formPerm [29, 60, 59] *
      List.formPerm [34, 36, 50] *
      List.formPerm [37, 42, 45]
  | 4 => List.formPerm [1, 8, 43] *
      List.formPerm [3, 5, 41] *
      List.formPerm [4, 62, 49] *
      List.formPerm [6, 33, 47] *
      List.formPerm [7, 36, 11] *
      List.formPerm [9, 44, 13] *
      List.formPerm [10, 19, 26] *
      List.formPerm [14, 18, 48] *
      List.formPerm [16, 61, 50] *
      List.formPerm [17, 23, 42] *
      List.formPerm [20, 28, 30] *
      List.formPerm [21, 27, 29] *
      List.formPerm [22, 55, 38] *
      List.formPerm [25, 46, 57] *
      List.formPerm [31, 56, 37] *
      List.formPerm [34, 40, 51] *
      List.formPerm [39, 53, 58] *
      List.formPerm [45, 59, 52]

@[expose] def evalW (g : Fin 5 → Equiv.Perm (Fin 63)) (w : List (Fin 5 × Bool)) : Equiv.Perm (Fin 63) :=
  (w.map fun l => cond l.2 (g l.1) (g l.1)⁻¹).prod

theorem vImg_relators : ∀ w ∈ u33PresRels, evalW vImg w = 1 := by decide +kernel

theorem lImg_relators : ∀ w ∈ u33PresRels, evalW lImg w = 1 := by decide +kernel

noncomputable def vHom : PG 5 u33PresRels →* Equiv.Perm (Fin 63) :=
  PresentedGroup.toGroup (f := vImg) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact vImg_relators w hw)

noncomputable def lHom : PG 5 u33PresRels →* Equiv.Perm (Fin 63) :=
  PresentedGroup.toGroup (f := lImg) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact lImg_relators w hw)

theorem vHom_of (i : Fin 5) : vHom (PresentedGroup.of i) = vImg i := by
  rw [vHom, PresentedGroup.toGroup.of]

theorem lHom_of (i : Fin 5) : lHom (PresentedGroup.of i) = lImg i := by
  rw [lHom, PresentedGroup.toGroup.of]

@[expose] def vTab : List String := ["", "YxyxY", "xy", "YXYxY", "xYXy", "yXYxy", "xYxy", "yxYXY", "xY", "YXyXY", "YxYXY", "xYXY", "yxyXY", "xYxY", "yXyXy", "yXYxY", "Xyxy", "yxyxy", "XYxY", "YXyXy", "yXY", "YxyXy", "YxY", "yxYXy", "XYXy", "yXyxY", "XyXy", "YxYXy", "YXy", "YXYXY", "yxY", "xyxY", "yxyxY", "xyxy", "yXyxy", "Xy", "YXYXy", "Y", "YxyXY", "xyXy", "yXYXY", "xyXY", "yxYxy", "y", "YxYxy", "XY", "YXyxY", "Yxyxy", "Yxy", "YXyxy", "yxy", "yxYxY", "XyxY", "yXyXY", "XYXY", "YXYxy", "yXy", "YxYxY", "YXY", "yXYXy", "XYxy", "yxyXy", "XyXY"]

@[expose] def lTab : List String := ["", "XyxyX", "xyxYx", "Yxyx", "x", "xyx", "xyX", "XyXyx", "xyxYX", "YXYx", "xYX", "xYXyX", "xYXyx", "yXYx", "xyXyX", "XYxyX", "xYx", "xYxyX", "xYxyx", "yxYX", "xyXyx", "XYXYx", "YXyX", "xyxyX", "XyXYx", "X", "YxYX", "xyxyx", "XyxYx", "xYXYX", "xYXYx", "XYXyX", "xyXYx", "yxyX", "xYxYx", "xYxYX", "XYxYx", "xyXYX", "yXyX", "Xyx", "Xyxyx", "yxyx", "XyXYX", "XYxYX", "XYx", "yXYX", "yX", "YxyX", "XYxyx", "Yx", "YxYx", "XYXyx", "XYX", "yXyx", "XyxYX", "XyX", "XyXyX", "YX", "YXyx", "YXYX", "XYXYX", "yxYx", "yx"]

theorem vTab_spec : ∀ j : Fin 63, evalW vImg (u33Word (vTab.getD j.val "")) 0 = j := by decide +kernel

theorem lTab_spec : ∀ j : Fin 63, evalW lImg (u33Word (lTab.getD j.val "")) 0 = j := by decide +kernel

theorem vImg_fix : vImg 0 0 = 0 ∧ vImg 1 0 = 0 ∧ vImg 2 0 = 0 ∧ vImg 3 0 = 0 := by decide +kernel

theorem lImg_fix : lImg 0 0 = 0 ∧ lImg 1 0 = 0 ∧ lImg 2 0 = 0 ∧ lImg 4 0 = 0 := by decide +kernel

@[expose] def cSet : List (Fin 63) := [0, 2, 8, 35, 37, 43, 45]

theorem fl_noPair : ∀ p q : Fin 63, p ≠ 0 → q ≠ 0 → p ≠ q →
    ¬ (∀ i ∈ [(0 : Fin 5), 1, 2, 3], (vImg i p = p ∨ vImg i p = q) ∧ (vImg i q = p ∨ vImg i q = q)) := by
  decide +kernel

theorem lImg_four_fix : (Finset.univ.filter fun i : Fin 63 => lImg 4 i = i).card = 9 := by decide +kernel

end CFSG.Quasithin.ModD

module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD9b

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_q9_swap67 (W : SMV 8) :
    hdRo7SmAAux_q9 (Equiv.swap (Fin.castSucc (Fin.castSucc (Fin.last 6)))
        (Fin.succ (Fin.castSucc (Fin.last 6)))) W =
      hdRo7SmAAux_permLin 8 (Equiv.swap (Fin.castSucc (Fin.last 6))
        (Fin.succ (Fin.last 6))) W := by
  change hdRo7SmAAux_proj9 (coordPerm 3 8
      (Equiv.swap (Fin.castSucc (Fin.castSucc (Fin.last 6)))
        (Fin.succ (Fin.castSucc (Fin.last 6)))) (hdRo7SmAAux_ext9 W)) =
    hdRo7SmAAux_permLin 8 (Equiv.swap (Fin.castSucc (Fin.last 6))
      (Fin.succ (Fin.last 6))) W
  ext i
  fin_cases i <;>
    simp [hdRo7SmAAux_proj9, hdRo7SmAAux_ext9, coordPerm_apply, hdRo7SmAAux_permLin_apply,
      Equiv.swap_apply_def]

theorem hdRo7SmAAux_d9Hom_swap_67_apply (v : SMV 7) :
    hdRo7SmAAux_d9Hom
        (Equiv.swap (Fin.castSucc (Fin.castSucc (Fin.last 6)))
          (Fin.succ (Fin.castSucc (Fin.last 6)))) v =
      v - smDual sm7A7b.2 v • sm7A7b.1 := by
  change hdRo7SmAAux_delProj (hdRo7SmAAux_q9
      (Equiv.swap (Fin.castSucc (Fin.castSucc (Fin.last 6)))
        (Fin.succ (Fin.castSucc (Fin.last 6)))) (hdRo7SmAAux_delEmbed v)) =
      v - smDual sm7A7b.2 v • sm7A7b.1
  rw [hdRo7SmAAux_q9_swap67]
  change hdRo7SmAAux_d8Hom
      (Equiv.swap (Fin.castSucc (Fin.last 6)) (Fin.succ (Fin.last 6))) v =
      v - smDual sm7A7b.2 v • sm7A7b.1
  exact hdRo7SmAAux_d8Hom_swap_last_apply v

theorem hdRo7SmAAux_d9Hom_swap_67_smRefl :
    SMRefl (hdRo7SmAAux_d9Hom
        (Equiv.swap (Fin.castSucc (Fin.castSucc (Fin.last 6)))
          (Fin.succ (Fin.castSucc (Fin.last 6))))) sm7A7b.1 (smDual sm7A7b.2) :=
  ⟨by
    rw [hdRo7SmAAux_smDual_apply, smDot]
    simp [sm7A7b, Fin.sum_univ_seven],
   fun v => hdRo7SmAAux_d9Hom_swap_67_apply v⟩

theorem hdRo7SmAAux_d9Hom_swap_inner' (k : Fin 8) (hk : k.val < 6) :
    hdRo7SmAAux_d9Hom (Equiv.swap k.castSucc k.succ) =
      hdRo7SmAAux_permLin 7 (Equiv.swap ⟨k.val, by omega⟩ ⟨k.val + 1, by omega⟩) := by
  have h := hdRo7SmAAux_d9Hom_swap_inner (⟨k.val, hk⟩ : Fin 6)
  simpa using h

theorem hdRo7SmAAux_d9Hom_swap_isRefl (k : Fin 8) :
    GGLinRefl (hdRo7SmAAux_d9Hom (Equiv.swap k.castSucc k.succ)) := by
  by_cases hk : k.val < 6
  · rw [hdRo7SmAAux_d9Hom_swap_inner' k hk]
    exact hdRo7SmAAux_permLin_swap_isRefl 6 ⟨k.val, hk⟩
  · by_cases h6 : k.val = 6
    · have hk6 : k = (6 : Fin 8) := Fin.ext h6
      rw [hk6]
      exact hdRo7SmAAux_isRefl_of_smRefl hdRo7SmAAux_d9Hom_swap_67_smRefl
    · have h7 : k = (7 : Fin 8) := Fin.ext (by omega)
      rw [h7]
      exact hdRo7SmAAux_isRefl_of_smRefl hdRo7SmAAux_d9Hom_swap_78_smRefl

end CFSG.StandardType.HdRo7SU.Small

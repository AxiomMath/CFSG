module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD9

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_d9Hom_swap_78_apply (v : SMV 7) :
    hdRo7SmAAux_d9Hom
        (Equiv.swap (Fin.castSucc (Fin.last 7)) (Fin.succ (Fin.last 7))) v =
      v - smDual sm7cx.2 v • sm7cx.1 := by
  change hdRo7SmAAux_delProj (hdRo7SmAAux_q9
      (Equiv.swap (Fin.castSucc (Fin.last 7)) (Fin.succ (Fin.last 7)))
      (hdRo7SmAAux_delEmbed v)) = v - smDual sm7cx.2 v • sm7cx.1
  rw [show hdRo7SmAAux_q9
      (Equiv.swap (Fin.castSucc (Fin.last 7)) (Fin.succ (Fin.last 7))) =
      kRefl 3 7 from hdRo7SmAAux_q9Hom_swap_last]
  ext i
  fin_cases i <;>
    simp [hdRo7SmAAux_delProj, hdRo7SmAAux_delEmbed, kRefl_apply, kRoot, sm7cx, smDual,
      Fin.sum_univ_seven, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  all_goals
    rw [show (2 : ZMod 3) = -1 by decide]
    simp only [show ∀ x : ZMod 3, x * (-1 : ZMod 3) = -x from fun x => mul_neg_one x]
    abel

theorem hdRo7SmAAux_d9Hom_swap_78_smRefl :
    SMRefl (hdRo7SmAAux_d9Hom
        (Equiv.swap (Fin.castSucc (Fin.last 7)) (Fin.succ (Fin.last 7))))
      sm7cx.1 (smDual sm7cx.2) :=
  ⟨by
    rw [hdRo7SmAAux_smDual_apply, smDot]
    simp [sm7cx, Fin.sum_univ_seven]
    decide,
   fun v => hdRo7SmAAux_d9Hom_swap_78_apply v⟩

end CFSG.StandardType.HdRo7SU.Small

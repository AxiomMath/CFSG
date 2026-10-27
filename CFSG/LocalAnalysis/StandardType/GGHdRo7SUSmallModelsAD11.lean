module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAD10

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SmAAux_d9Hom_swap_08_apply (v : SMV 7) :
    hdRo7SmAAux_d9Hom (Equiv.swap (0 : Fin 9) (Fin.last 8)) v =
      v - smDual sm7A7a.2 v • sm7A7a.1 := by
  change hdRo7SmAAux_delProj (hdRo7SmAAux_q9 (Equiv.swap (0 : Fin 9) (Fin.last 8))
      (hdRo7SmAAux_delEmbed v)) = v - smDual sm7A7a.2 v • sm7A7a.1
  ext i
  fin_cases i <;>
    simp [hdRo7SmAAux_delProj, hdRo7SmAAux_delEmbed, hdRo7SmAAux_q9, hdRo7SmAAux_q9Hom,
      hdRo7SmAAux_proj9, hdRo7SmAAux_ext9, LinearMap.pi_apply, Equiv.swap_apply_def,
      sm7A7a, smDual, Fin.sum_univ_seven, Pi.sub_apply, Pi.smul_apply, Pi.single_apply]
  all_goals
    generalize v 0 = a
    clear v
    revert a
    decide

end CFSG.StandardType.HdRo7SU.Small

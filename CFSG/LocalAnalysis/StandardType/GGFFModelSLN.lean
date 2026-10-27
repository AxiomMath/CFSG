module

public import CFSG.LocalAnalysis.StandardType.GGFFModelNDefs
public import CFSG.LocalAnalysis.StandardType.GGFFSLNDefs
import CFSG.LocalAnalysis.StandardType.GGFFSLNExp
import CFSG.LocalAnalysis.StandardType.GGFFSLNCen
import CFSG.LocalAnalysis.StandardType.GGFFSLNRoot
import CFSG.LocalAnalysis.StandardType.GGFFSLNOut
import CFSG.LocalAnalysis.StandardType.GGFFSLNO2
import CFSG.LocalAnalysis.StandardType.GGFFSLNSyl7

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.GGFF

open scoped MatrixGroups
open CFSG.RankThree.PartTwo.Sec4.RonanK429F

theorem modelN_SL6 : ModelN SL(6, ZMod 2) W6.T where
  cen := cen_SL6
  out := out_SL (by norm_num)
  o2 := o2_SL6_of_cen cen_SL6
  caseA := caseA_SL6
  syl7 := syl7_SL6
  caseB := ⟨W6.tw, N6.x0, N6.r, N6.r', W6.pow_tw, pi_z_SL6, x0_z0_SL6, x0_z1_SL6, x0_z2_SL6,
    sqrt_SL6, root_sq_SL6, root_comm_SL6, root_rel_SL6, root_char_SL6, root_dist_SL6, braid_SL6,
    braid_eq_SL6, g_pow_SL6, g_ne_SL6, g_out_SL6⟩

theorem modelN_SL7 : ModelN SL(7, ZMod 2) W7.T where
  cen := cen_SL7
  out := out_SL (by norm_num)
  o2 := o2_SL7_of_cen cen_SL7
  caseA := caseA_SL7
  syl7 := syl7_SL7
  caseB := ⟨W7.tw, N7.x0, N7.r, N7.r', W7.pow_tw, pi_z_SL7, x0_z0_SL7, x0_z1_SL7, x0_z2_SL7,
    sqrt_SL7, root_sq_SL7, root_comm_SL7, root_rel_SL7, root_char_SL7, root_dist_SL7, braid_SL7,
    braid_eq_SL7, g_pow_SL7, g_ne_SL7, g_out_SL7⟩

end CFSG.StandardType.GGFF

end

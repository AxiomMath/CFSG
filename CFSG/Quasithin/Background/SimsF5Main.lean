module

public import CFSG.Quasithin.Background.SimsF5Par
public import CFSG.Quasithin.Background.SimsF5S6

public section

namespace CFSG.Quasithin.SimsF5

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Open

theorem f51 : F51 := by
  refine ⟨⟨isL43_MDot, fun J hJ _ => ⟨eJ_mem_OVq J, eJ_mul_self J, commSp_eJ J, fixSp_eJ J hJ,
      eq_eJ_of_commSp J⟩⟩, ⟨M0Dot_eq, ⟨GDotEquiv⟩, isGenLie_GDot,
      ⟨fDot_mem_MDot, fDot_mul_self, fDot_smul_x3, fDot_smul_x4, fDot_smul_x5, fDot_smul_x6,
        fDot_smul_x1⟩, fun g _ => eq_fDot_of g⟩, ⟨⟨M0DotEquivPO5⟩, isAutU42_M0Dot⟩,
    ⟨commSp_fDot, finrank_V2minus, signMinus_V2minus, fixSp_fDot, finrank_V4minus,
      signMinus_V4minus⟩, ⟨DDot_eq, blk4_injOn_CGDot12, blk4_image,
      ⟨zDot_mem_GDot, zDot_mul_self, commSp_zDot, finrank_V4plus, signPlus_V4plus⟩,
      neg_zDot_refl, ⟨DDotEquivS6⟩⟩⟩

theorem f52 : F52 := by
  refine ⟨M1Dot_eq_stab, ⟨Q2Dot_coe, isEn_Q2Dot, Q2Dot_le_M2Dot, Q2Dot_normal,
      mono_M2Dot_complement, M1Dot_structure⟩, ⟨isAutU42_M0Dot, M1Dot_le_M0Dot, M2Dot_le_M0Dot,
      mono_M1Dot_ne_M2Dot, rfl, isSylowOf_TDot_M12, isSylowOf_TDot_MDot,
      maximal_overgroups_TDot⟩⟩

end CFSG.Quasithin.SimsF5

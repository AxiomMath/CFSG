module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDetCoord
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggDetAut_ggSL9ShiftCoord :
    ((ggDetAut 7 (by norm_num) (fun a b => mul_comm a b)
      (fun a => pow_eq_one_of_multiplicative_fin_zmod a) ggSL9ShiftCoord : (ZMod 7)ˣ) :
      ZMod 7) = 2 := by
  rw [ggDetAut_coord (by norm_num) _ _ ggSL9ShiftCoord (MulEquiv.refl _)
    !![0, 0, 2; 1, 0, 0; 0, 1, 0]]
  · simp [Matrix.det_fin_three]
  · intro f
    show Multiplicative.toAdd (ggSL9ShiftCoord (Multiplicative.ofAdd f)) = _
    rw [ggSL9ShiftCoord_apply]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end CFSG.StandardType

end

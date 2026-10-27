module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.Quasithin.RonanF57

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {K : Type} [Field K]

theorem bar_eq_sq (h : UnitaryFieldData 2 1 K) (x : K) : h.bar x = x ^ 2 := by
  rw [h.bar_apply]; norm_num

end CFSG.Quasithin.RonanF57

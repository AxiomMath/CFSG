module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKFormDefs

public section

namespace CFSG.StandardType

namespace E6Dep

@[expose] def gbetaR (c r : ZMod 3) : Mat6 :=
  !![1, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 0; 0, 1, 1, 1, 0, 0; 0, 0, 1, 1, 0, 0;
    0, 0, 0, 0, r * (c * c), -(r * c); 0, 0, 0, 0, -(r * c), r]

theorem gbetaR_one (c : ZMod 3) : gbetaR c 1 = gbeta c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gbetaR, gbeta]

theorem kY_eq (c : ZMod 3) : kY c = xs + c • xx := by
  ext i
  fin_cases i <;> simp [kY, xs, xx]

end E6Dep

end CFSG.StandardType

end

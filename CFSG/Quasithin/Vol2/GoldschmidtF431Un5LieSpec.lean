module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieStdTwo
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieStdV
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieBrA

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.Sec53F.Unit

variable {F : Type} [Field F] (hF : Nat.card F = (2 ^ 2) ^ 2)

theorem stdTwo_un5Y :
    Lift.StdTwo (hypPSU (un5FD hF) 2 1) (hypProjUnitriangular (un5FD hF) 2 1)
      (u5PtP (un5FD hF)) (u5LnP (un5FD hF)) (z5Y (un5FD hF)) (t5Y (un5FD hF)) :=
  stdTwo_Y (le_refl 2)

theorem unStdV_un5Y :
    UnStdV (hypPSU (un5FD hF) 2 1) (hypProjUnitriangular (un5FD hF) 2 1)
      (u5PtP (un5FD hF)) (u5LnP (un5FD hF)) (z5Y (un5FD hF)) (t5Y (un5FD hF))
      (v5Y (un5FD hF)) :=
  unStdV_Y (le_refl 2)

end CFSG.Quasithin.H13.F431.Un

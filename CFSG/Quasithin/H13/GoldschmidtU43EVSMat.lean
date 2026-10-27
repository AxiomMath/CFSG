module

public import CFSG.Quasithin.H13.GoldschmidtU43EVR4

public section

namespace CFSG.Quasithin.H13.U43

set_option maxRecDepth 100000 in
theorem cube_Umat_Zmat_Rho3mat : (Umat * Zmat * Rho3mat) ^ 3 = 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem cube_Umat_Vmat_Rho3mat_Rho4mat :
    (Umat * Vmat * (Rho3mat * Rho3mat) * Rho4mat) ^ 3 = 1 := by decide +kernel

end CFSG.Quasithin.H13.U43

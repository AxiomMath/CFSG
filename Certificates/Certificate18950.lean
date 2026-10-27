module

public import CFSG.Quasithin.H13.U3SixCodes

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

private theorem cert18950_hsingle : ∀ i : Fin 6, vecOf (2 ^ (i : ℕ)) = Pi.single i 1 := by
  decide +kernel

end CFSG.Quasithin.H13.U3

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 Matrix in
theorem certificate18950 : ∀ i : Fin 6, vecOf (2 ^ (i : ℕ)) = Pi.single i 1 := by
  exact CFSG.Quasithin.H13.U3.cert18950_hsingle

end Certificates

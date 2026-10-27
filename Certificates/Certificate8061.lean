module

import CFSG.Certificates.Kernel.B3SixDSound
import Certificates.Kernel.B3Six.DL
import Certificates.Kernel.B3Six.DGU0
import Certificates.Kernel.B3Six.DGUT0
public import CFSG.Quasithin.Background.B3FourData
public import Certificates.Certificate8063

public section

open CFSG.Quasithin.B3 CFSG.KC.B3Six

namespace Certificates

open CFSG CFSG.Quasithin CFSG.Quasithin.B3 in
theorem certificate8061 : (chkL6 Mod.u0 = true)
    ∧ (chkL6 Mod.ut0 = true)
    ∧ (chkG6 Mod.u0 = true)
    ∧ (chkG6 Mod.ut0 = true) :=
  ⟨chkL6_of_D _ _ CFSG.KD.B3SixDL.eq_u0 CFSG.KD.B3SixDL.struct_u0 CFSG.KD.B3SixDL.sub_u0
      CFSG.KD.B3SixDL.r_u0,
    chkL6_of_D _ _ CFSG.KD.B3SixDL.eq_ut0 CFSG.KD.B3SixDL.struct_ut0 CFSG.KD.B3SixDL.sub_ut0
      CFSG.KD.B3SixDL.r_ut0,
    chkG6_of_D _ _ CFSG.KD.B3SixDGU0.eq_ok CFSG.KD.B3SixDGU0.struct_ok CFSG.KD.B3SixDGU0.gen_ok
      CFSG.KD.B3SixDGU0.sub_ok CFSG.KD.B3SixDGU0.wit_ok CFSG.KD.B3SixDGU0.rg_ok,
    chkG6_of_D _ _ CFSG.KD.B3SixDGUT0.eq_ok CFSG.KD.B3SixDGUT0.struct_ok
      CFSG.KD.B3SixDGUT0.gen_ok CFSG.KD.B3SixDGUT0.sub_ok CFSG.KD.B3SixDGUT0.wit_ok
      CFSG.KD.B3SixDGUT0.rg_ok⟩

end Certificates

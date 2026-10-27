
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8Table
import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8TableWreathBase
import CFSG.Certificates.Kernel.TS8WrKSound2
import Certificates.Kernel.TS8Wr.Checks27801

public section

namespace Certificates

open CFSG.KD.TS8Wr in
theorem certificate27801 : CFSG.EvenSporadicStandard.Fin76b.OuterTableWreath :=
  CFSG.EvenSporadicStandard.Fin76b.outerTableWreath_of_noTabSig
    (CFSG.KC.TS8WrK.noTabSig_of_checks tb_ok p0_ok rt_ok z_ok za_ok ch27801r_all)

end Certificates

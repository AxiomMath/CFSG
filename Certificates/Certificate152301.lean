module

public import Certificates.Data.ONFrobenius
public import Certificates.Data.CFSGNative.SectionRank.F3
import CFSG.Certificates.Kernel.OpsFrobSound
import Certificates.Kernel.Frob.ON
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.KD.LC.F3

open CFSG.SectionRank.Native in
theorem certificate152301 : (ops3 154).frobCheck onFrobData = true :=
  CFSG.KC.OpsFrob.frobCheck_of_L ON.lay_ok rfl rfl ON.decA ON.decB
    ((rfl : onFrobData.seedA = CFSG.Blueprint.NativeSporadic.ONSeed1).trans ON.LA_eq)
    ((rfl : onFrobData.seedB = CFSG.Blueprint.NativeSporadic.ONSeed2).trans ON.LB_eq)
    KernelFrob.ON.frob_K

end Certificates

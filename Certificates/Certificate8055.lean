module

public import CFSG.Timmesfeld.Exceptional.DeepQData
import Certificates.Kernel.Misc.Coset.C8055
public import CFSG.Certificates.CosetTablePresented

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Timmesfeld CFSG.Timmesfeld.Moufang CFSG.Timmesfeld.Moufang.Deep CFSG.CosetTable in
theorem certificate8055 : PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk} (FreeGroup.mk wQC6) ∈
    genSub {r : FreeGroup (Fin 3) | r ∈ relsQ.map FreeGroup.mk} (subsetOf 3 [0, 1]) := KernelMiscCoset.C8055.mem

end Certificates

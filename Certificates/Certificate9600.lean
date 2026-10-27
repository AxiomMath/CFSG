module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaThData
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaGrp.Th
import Certificates.Kernel.McertP.Glue
import CFSG.Certificates.Kernel.AlphaGrpKSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaTh

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaTh
  CFSG.Blueprint.NativeSporadic in
theorem certificate9600 : modCheckW (ops2 248) ThSeed1 ThSeed2 thNregs thProg 3 thMod
    thTops thTidx 10 thCf thCi thCt = true := by
  exact modCheckW_of_N (hom2 248 (by norm_num)) KernelMC.thA KernelMC.thB trivial trivial
    KernelAG.th_K KernelAG.th_wf KernelAG.th_pc KernelAG.th_top
    (KernelMP.wOK_of KernelAG.th_wTops KernelAG.th_wNodup KernelAG.th_wCount)
    (by decide) KernelAG.th_fun
    (altOK_of_altW (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) KernelAG.th_alt)

end Certificates

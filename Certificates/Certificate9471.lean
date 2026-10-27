module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.BetaFusMcLInputs
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.OpsLayFusSound
import Certificates.Kernel.FusLay.McL

public section

open CertificateChecks.KernelFusLay

namespace Certificates

open CFSG.SectionRank.Native CFSG.RankThree.PartOne.CTP.Fus CFSG.Blueprint in
theorem certificate9471 : fusCheck (ops3 21) NativeSporadic.McLSeed1 NativeSporadic.McLSeed2
    betaMcLP3N betaMcLP3Prog betaMcLP3 = true :=
  CFSG.KC.OpsLayK.fusL_sound McL.lay_ok rfl rfl McL.decA McL.decB McL.LA_eq McL.LB_eq
    McL.fus9471_K

end Certificates

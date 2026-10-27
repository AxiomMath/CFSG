module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyThreeInputs
public import CFSG.Sporadic.Schreier.LyCheckCover
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueLy

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint CFSG.Sporadic.He.Native
  CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native in
theorem certificate9524 : lyCheck (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
    (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 0))
    (evalWordM seedM (seedMInv (powM 5 111 matB 4)) (seedWord 1)) lyThreeN lyThreeProg
    lyTzSpec lyCzSpec = true := KernelMC.lyThree

end Certificates

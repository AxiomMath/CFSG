module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveInputs
public import CFSG.Sporadic.Schreier.LyCheckSeven
public import Certificates.Data.CFSGNative.SectionRank.Fp
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.MatCert.GlueLy

public section

namespace Certificates

open CertificateChecks

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.Blueprint CFSG.Sporadic.He.Native
  CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native in
theorem certificate9525 : ly5Check (opsP 5 111) NativeSporadic.LySeed1 NativeSporadic.LySeed2
    [(pairAt (aStarArr (powM 5 111 matB 4)) 2).1, (pairAt (aStarArr (powM 5 111 matB 4)) 3).1,
      (pairAt (aStarArr (powM 5 111 matB 4)) 4).1, (pairAt (aStarArr (powM 5 111 matB 4)) 5).1,
      (pairAt (aStarArr (powM 5 111 matB 4)) 6).1] (fun X => !stabOK X) lyFiveN lyFiveProg
    lyTzSpec5 lyCzSpec5 = true := KernelMC.lyFive

end Certificates

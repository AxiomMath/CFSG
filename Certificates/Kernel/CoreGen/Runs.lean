module

public import Certificates.Data.Kernel.CoreGenN
public import Certificates.Kernel.LocalComp.ThOrder
public import Certificates.Kernel.MatCert.J4Seeds
public import Certificates.Kernel.MatCert.Fp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreThFiveData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreJ4ThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreHeThreeData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreHeSevenData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CertificateChecks.KernelCG

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
open CertificateChecks.KernelMC

theorem th_K : coreGenN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M CoreTh5.nregs CoreTh5.prog
    CoreTh5.spec = true := by
  quickRfl

theorem th_D : CoreTh5.spec.rA < CoreTh5.nregs ∧ CoreTh5.spec.rB < CoreTh5.nregs ∧
    CoreTh5.spec.wf = true := by
  decide +kernel

theorem j4_K : coreGenN (opsF2K 112) JA.M JB.M CoreJ43.nregs CoreJ43.prog CoreJ43.spec = true := by
  quickRfl

theorem j4_D : CoreJ43.spec.rA < CoreJ43.nregs ∧ CoreJ43.spec.rB < CoreJ43.nregs ∧
    CoreJ43.spec.wf = true := by
  decide +kernel

theorem he3_K : forceB (payHe HeS1.chars) (fun A => forceB (payHe HeS2.chars) fun B =>
    vldHe A && vldHe B && coreGenN O7 A B CoreHe3.nregs CoreHe3.prog CoreHe3.spec) = true := by
  quickRfl

theorem he3_D : CoreHe3.spec.rA < CoreHe3.nregs ∧ CoreHe3.spec.rB < CoreHe3.nregs ∧
    CoreHe3.spec.wf = true := by
  decide +kernel

theorem he7_K : forceB (payHe HeS1.chars) (fun A => forceB (payHe HeS2.chars) fun B =>
    vldHe A && vldHe B && coreGenN O7 A B CoreHe7.nregs CoreHe7.prog CoreHe7.spec) = true := by
  quickRfl

theorem he7_D : CoreHe7.spec.rA < CoreHe7.nregs ∧ CoreHe7.spec.rB < CoreHe7.nregs ∧
    CoreHe7.spec.wf = true := by
  decide +kernel

end CertificateChecks.KernelCG

end

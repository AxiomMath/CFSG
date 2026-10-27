module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo2Data
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.F2
import CFSG.Certificates.Kernel.OpsMcertNSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.SectionRank.Native CFSG.AGLEmbedding.R3
  CFSG.Blueprint

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo2
  CFSG.Blueprint.NativeSporadic in
theorem certificate9592 : modCheck (ops2 22) Co2Seed1 Co2Seed2 co2Nregs co2Prog 3 co2Mod
    co2Tops co2Tests co2Cf co2Ci co2Ct = true := by
  have hA : (ops2 22).decode NativeSporadic.Co2Seed1 = (hom2 22 (by norm_num)).U KernelAM.C2A.M := by
    rw [KernelAM.C2A.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C2A.bind
  have hB : (ops2 22).decode NativeSporadic.Co2Seed2 = (hom2 22 (by norm_num)).U KernelAM.C2B.M := by
    rw [KernelAM.C2B.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C2B.bind
  unfold modCheck
  rw [mcertCheck_of_N (hom2 22 (by norm_num)) hA hB trivial trivial KernelAM.co2_K, Bool.true_and]
  exact KernelAM.co2_D

end Certificates

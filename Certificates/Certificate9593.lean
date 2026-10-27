module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaCo3Data
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

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaCo3
  CFSG.Blueprint.NativeSporadic in
theorem certificate9593 : modCheck (ops2 22) Co3Seed1 Co3Seed2 co3Nregs co3Prog 3 co3Mod
    co3Tops co3Tests co3Cf co3Ci co3Ct = true := by
  have hA : (ops2 22).decode NativeSporadic.Co3Seed1 = (hom2 22 (by norm_num)).U KernelAM.C3A.M := by
    rw [KernelAM.C3A.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C3A.bind
  have hB : (ops2 22).decode NativeSporadic.Co3Seed2 = (hom2 22 (by norm_num)).U KernelAM.C3B.M := by
    rw [KernelAM.C3B.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelAM.C3B.bind
  unfold modCheck
  rw [mcertCheck_of_N (hom2 22 (by norm_num)) hA hB trivial trivial KernelAM.co3_K, Bool.true_and]
  exact KernelAM.co3_D

end Certificates

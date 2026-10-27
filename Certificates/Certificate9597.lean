module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaJ3Data
public import Certificates.Data.CFSGNative.SectionRank.F2
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaGrp.J3
import CFSG.Certificates.Kernel.AlphaGrpKSound
import CFSG.Certificates.Kernel.OpsKSound

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsK CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaJ3
  CFSG.Blueprint

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaJ3
  CFSG.Blueprint.NativeSporadic in
theorem certificate9597 : modCheckE (ops2 80) J3Seed1 J3Seed2 j3Nregs j3Prog 3 j3Mod
    j3Tops j3Gs j3Cf j3Ci j3Ct = true := by
  have hA : (ops2 80).decode NativeSporadic.J3Seed1 =
      (hom2 80 (by norm_num)).U KernelJ3L.JA.M := by
    rw [KernelJ3L.JA.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelJ3L.JA.bind
  have hB : (ops2 80).decode NativeSporadic.J3Seed2 =
      (hom2 80 (by norm_num)).U KernelJ3L.JB.M := by
    rw [KernelJ3L.JB.eq]
    exact CFSG.KC.Co1F2.bind_sound KernelJ3L.JB.bind
  exact modCheckE_of_N (hom2 80 (by norm_num)) hA hB trivial trivial KernelAG.j3_K
    KernelAG.j3_wf KernelAG.j3_pc KernelAG.j3_ent KernelAG.j3_top KernelAG.j3_grp
    (by decide) KernelAG.j3_fun
    (altOK_of_altW (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) KernelAG.j3_alt)

end Certificates

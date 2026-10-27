module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi22Data
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.Fi22
import CFSG.Certificates.Kernel.OpsLayMcertSound
import CFSG.Certificates.Kernel.AlphaFunKSound

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi22 CertificateChecks.KernelAM

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi22
  CFSG.Blueprint.NativeSporadic in
theorem certificate9595 : modCheckE (ops3 77) Fi22Seed1 Fi22Seed2 fi22Nregs fi22Prog 3 fi22Mod
    fi22Tops fi22Gs fi22Cf fi22Ci fi22Ct = true := by
  have hfun : fi22Mod.funOK 3 fi22Cf = true := funOK_of_funW (fun _ _ _ => rfl) fi22_fun
  have halt : fi22Mod.altOK 3 fi22Ci fi22Ct tgtAlt = true :=
    altOK_of_altW (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) fi22_alt
  unfold modCheckE
  rw [mcertL_sound (d := 77) KernelTc.Fi22.lay_ok rfl rfl KernelTc.Fi22.decA KernelTc.Fi22.decB
    KernelTc.Fi22.LA_eq KernelTc.Fi22.LB_eq fi22_K, fi22_wf, fi22_pc, fi22_ent, fi22_top,
    fi22_grp, decide_eq_true (by decide : 3 ≤ fi22Mod.basis.length), hfun, halt]
  rfl

end Certificates

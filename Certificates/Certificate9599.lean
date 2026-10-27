module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi23Data
public import Certificates.Data.CFSGNative.SectionRank.F3
public import CFSG.Blueprint.NativeSporadic
import Certificates.Kernel.AlphaMc.Fi23
import Certificates.Kernel.AlphaMc.Fi23Data
import Certificates.Kernel.McertP.Glue
import CFSG.Certificates.Kernel.AlphaFunKSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

public section

set_option maxRecDepth 400000

namespace Certificates

open CertificateChecks

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi23 CertificateChecks.KernelTc
  CertificateChecks.KernelAM.Fi23

open CFSG.SectionRank.Native CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi23
  CFSG.Blueprint.NativeSporadic in
theorem certificate9599 : modCheckW (ops3 253) Fi23Seed1 Fi23Seed2 fi23Nregs fi23Prog 3 fi23Mod
    fi23Tops fi23Tidx 13 fi23Cf fi23Ci fi23Ct = true := by
  obtain ⟨hm, -⟩ := seedsLC_sound (C := ⟨fi23Nregs, fi23Prog, fi23Mod.modFactsW 3 fi23Tops⟩)
    (S := fun i => W.SL.getD i []) (k := 200) (m := 4) (kf := 1) (mf := 421) (rA := 0) (rB := 1)
    (d := 253) Fi23.lay_ok rfl rfl Fi23.decA Fi23.decB Fi23.LA_eq Fi23.LB_eq (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (eq_of_eqL init) (by decide +kernel) ch_all
    (by decide +kernel) fa_all seeds
  have hfun : fi23Mod.funOK 3 fi23Cf = true := funOK_of_funW (fun _ _ _ => rfl) w_fun
  have halt : fi23Mod.altOK 3 fi23Ci fi23Ct tgtAlt = true :=
    altOK_of_altW (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl) w_alt
  unfold modCheckW
  rw [hm, w_wf, w_pc, w_top, KernelMP.wOK_of w_wTops w_wNodup w_wCount,
    decide_eq_true (by decide : 3 ≤ fi23Mod.basis.length), hfun, halt]
  rfl

end Certificates

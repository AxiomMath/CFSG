module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.TcGen.Fi23
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi23Data
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi23Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

set_option maxRecDepth 400000
set_option Elab.async false

#lay_snaps CertificateChecks.KernelAM.Fi23.W 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CFSG.AGLEmbedding.R3.AlphaFi23.fi23Prog 39 200

public section

namespace CertificateChecks.KernelAM.Fi23

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi23 CertificateChecks.KernelTc.Fi23

@[expose] noncomputable def ch (i : Nat) : Bool :=
  chunkL lay fi23Prog 200 i (W.SL.getD i []) (W.SL.getD (i + 1) [])

@[expose] noncomputable def fa (i : Nat) : Bool :=
  factsL lay (W.SL.getD 4 []) fi23Nregs (fi23Mod.modFactsW 3 fi23Tops) 1 i

theorem init : eqL (W.SL.getD 0 []) (initR lay A B fi23Nregs) = true := by quickRfl

#kc_each ch 0 4
#kc_each fa 0 421

#kc_forall_tree ch_all (fun i => ch i = true) 4 CertificateChecks.KernelAM.Fi23.ch
#kc_forall_tree fa_all (fun i => fa i = true) 421 CertificateChecks.KernelAM.Fi23.fa

theorem seeds : seedRegsL lay (W.SL.getD 4 []) A B 0 1 = true := by quickRfl

theorem ch_neg : (!chunkL lay fi23Prog 200 0 (W.SL.getD 0 []) (W.SL.getD 0 [])) = true := by
  quickRfl

theorem fa_neg : (!factsL lay (W.SL.getD 0 []) fi23Nregs (fi23Mod.modFactsW 3 fi23Tops) 1 15) =
    true := by
  quickRfl

theorem seeds_neg : (!seedRegsL lay (W.SL.getD 4 []) B A 0 1) = true := by
  quickRfl

end CertificateChecks.KernelAM.Fi23

end

module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySnaps
public import Certificates.Kernel.TcGen.Fi23
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi23Data
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaFi23Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LocalQT.RunF3Sound
import Certificates.Kernel.LocalComp.LayF3Cuts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs
meta import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaWordDefs

set_option maxRecDepth 400000
set_option Elab.async false

#lay_snaps CertificateChecks.KernelAM.Fi23.W 3 253 CertificateChecks.KernelTc.Fi23.A
  CertificateChecks.KernelTc.Fi23.B CFSG.AGLEmbedding.R3.AlphaFi23.fi23Prog 39 200

#lay_f3_cuts_l CertificateChecks.KernelAM.Fi23.F3c0 3 253 16 CertificateChecks.KernelAM.Fi23.W.S0
  CFSG.AGLEmbedding.R3.AlphaFi23.fi23Prog 200 0 [49, 90, 124, 173]
#lay_f3_cuts_l CertificateChecks.KernelAM.Fi23.F3c1 3 253 16 CertificateChecks.KernelAM.Fi23.W.S1
  CFSG.AGLEmbedding.R3.AlphaFi23.fi23Prog 200 1 [53, 102, 164]
#lay_f3_cuts_l CertificateChecks.KernelAM.Fi23.F3c2 3 253 16 CertificateChecks.KernelAM.Fi23.W.S2
  CFSG.AGLEmbedding.R3.AlphaFi23.fi23Prog 200 2 [63, 125, 186]
#lay_f3_cuts_l CertificateChecks.KernelAM.Fi23.F3c3 3 253 16 CertificateChecks.KernelAM.Fi23.W.S3
  CFSG.AGLEmbedding.R3.AlphaFi23.fi23Prog 200 3 [62]

public section

namespace CertificateChecks.KernelAM.Fi23

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.AlphaFi23 CertificateChecks.KernelTc.Fi23
open CFSG.KC.OpsLayF3

@[expose] noncomputable def ch (i : Nat) : Bool :=
  chunkL lay fi23Prog 200 i (W.SL.getD i []) (W.SL.getD (i + 1) [])

@[expose] noncomputable def fa (i : Nat) : Bool :=
  factsL lay (W.SL.getD 4 []) fi23Nregs (fi23Mod.modFactsW 3 fi23Tops) 1 i

theorem init : eqL (W.SL.getD 0 []) (initR lay A B fi23Nregs) = true := by quickRfl

theorem f3good : Good lay 16 := ⟨lay_ok, rfl, by decide, by decide⟩

theorem f3p0_0 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (0 * 200)).take 200).drop 0).take (49 - 0))
      (gL lay 16 (W.SL.getD 0 []))
      (fun R => eqVL R F3c0.M1) = true := by quickRfl

theorem f3p0_1 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (0 * 200)).take 200).drop 49).take (90 - 49))
      F3c0.M1
      (fun R => eqVL R F3c0.M2) = true := by quickRfl

theorem f3p0_2 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (0 * 200)).take 200).drop 90).take (124 - 90))
      F3c0.M2
      (fun R => eqVL R F3c0.M3) = true := by quickRfl

theorem f3p0_3 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (0 * 200)).take 200).drop 124).take (173 - 124))
      F3c0.M3
      (fun R => eqVL R F3c0.M4) = true := by quickRfl

theorem f3p0_4 :
    runV (ctxOf lay 16) (((fi23Prog.drop (0 * 200)).take 200).drop 173)
      F3c0.M4
      (fun R => eqVL R (gL lay 16 (W.SL.getD (0 + 1) []))) = true := by quickRfl

theorem f3v0 : (allValid lay (W.SL.getD 0 []) && allValid lay (W.SL.getD (0 + 1) [])) = true := by
  quickRfl

theorem ch0 : ch (nat_lit 0) = true :=
  chunkL_of_F3 f3good (chunkL3_intro f3v0
    (runV_split (by decide) f3p0_0
      (runV_split (by decide) f3p0_1
      (runV_split (by decide) f3p0_2
      (runV_split (by decide) f3p0_3
      f3p0_4)))))

theorem f3p1_0 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (1 * 200)).take 200).drop 0).take (53 - 0))
      (gL lay 16 (W.SL.getD 1 []))
      (fun R => eqVL R F3c1.M1) = true := by quickRfl

theorem f3p1_1 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (1 * 200)).take 200).drop 53).take (102 - 53))
      F3c1.M1
      (fun R => eqVL R F3c1.M2) = true := by quickRfl

theorem f3p1_2 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (1 * 200)).take 200).drop 102).take (164 - 102))
      F3c1.M2
      (fun R => eqVL R F3c1.M3) = true := by quickRfl

theorem f3p1_3 :
    runV (ctxOf lay 16) (((fi23Prog.drop (1 * 200)).take 200).drop 164)
      F3c1.M3
      (fun R => eqVL R (gL lay 16 (W.SL.getD (1 + 1) []))) = true := by quickRfl

theorem f3v1 : (allValid lay (W.SL.getD 1 []) && allValid lay (W.SL.getD (1 + 1) [])) = true := by
  quickRfl

theorem ch1 : ch (nat_lit 1) = true :=
  chunkL_of_F3 f3good (chunkL3_intro f3v1
    (runV_split (by decide) f3p1_0
      (runV_split (by decide) f3p1_1
      (runV_split (by decide) f3p1_2
      f3p1_3))))

theorem f3p2_0 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (2 * 200)).take 200).drop 0).take (63 - 0))
      (gL lay 16 (W.SL.getD 2 []))
      (fun R => eqVL R F3c2.M1) = true := by quickRfl

theorem f3p2_1 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (2 * 200)).take 200).drop 63).take (125 - 63))
      F3c2.M1
      (fun R => eqVL R F3c2.M2) = true := by quickRfl

theorem f3p2_2 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (2 * 200)).take 200).drop 125).take (186 - 125))
      F3c2.M2
      (fun R => eqVL R F3c2.M3) = true := by quickRfl

theorem f3p2_3 :
    runV (ctxOf lay 16) (((fi23Prog.drop (2 * 200)).take 200).drop 186)
      F3c2.M3
      (fun R => eqVL R (gL lay 16 (W.SL.getD (2 + 1) []))) = true := by quickRfl

theorem f3v2 : (allValid lay (W.SL.getD 2 []) && allValid lay (W.SL.getD (2 + 1) [])) = true := by
  quickRfl

theorem ch2 : ch (nat_lit 2) = true :=
  chunkL_of_F3 f3good (chunkL3_intro f3v2
    (runV_split (by decide) f3p2_0
      (runV_split (by decide) f3p2_1
      (runV_split (by decide) f3p2_2
      f3p2_3))))

theorem f3p3_0 :
    runV (ctxOf lay 16) ((((fi23Prog.drop (3 * 200)).take 200).drop 0).take (62 - 0))
      (gL lay 16 (W.SL.getD 3 []))
      (fun R => eqVL R F3c3.M1) = true := by quickRfl

theorem f3p3_1 :
    runV (ctxOf lay 16) (((fi23Prog.drop (3 * 200)).take 200).drop 62)
      F3c3.M1
      (fun R => eqVL R (gL lay 16 (W.SL.getD (3 + 1) []))) = true := by quickRfl

theorem f3v3 : (allValid lay (W.SL.getD 3 []) && allValid lay (W.SL.getD (3 + 1) [])) = true := by
  quickRfl

theorem ch3 : ch (nat_lit 3) = true :=
  chunkL_of_F3 f3good (chunkL3_intro f3v3
    (runV_split (by decide) f3p3_0
      f3p3_1))

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

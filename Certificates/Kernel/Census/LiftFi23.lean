module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.Fi23Lift
public import Certificates.Kernel.LocalComp.F3.Fi23
public import Certificates.Kernel.LocalComp.LaySnapsChunksF
public import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.LocalQT.RunF3Sound
import Certificates.Kernel.LocalComp.LayF3Cuts

set_option maxRecDepth 400000
set_option Elab.async false

#kc_repo #kc_json CertificateChecks.KernelCensus.LiftFi23
  "Certificates/Kernel/Census/data/liftfi23.json" 16045 249258710014154195
  (cs : List CFSG.KC.OpsLayK.RChunk)

#lay_snaps_chunks_f CertificateChecks.KernelCensus.LiftFi23 3 253
  CFSG.KD.LC.F3.Fi23.A CFSG.KD.LC.F3.Fi23.B CertificateChecks.KernelCensus.LiftFi23.cs

#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k0 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S0
  CertificateChecks.KernelCensus.LiftFi23.cs 0 [60, 120]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k1 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S1
  CertificateChecks.KernelCensus.LiftFi23.cs 1 [60, 120]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k2 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S2
  CertificateChecks.KernelCensus.LiftFi23.cs 2 [38, 75, 111, 147]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k3 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S3
  CertificateChecks.KernelCensus.LiftFi23.cs 3 [34, 67, 98, 132]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k4 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S4
  CertificateChecks.KernelCensus.LiftFi23.cs 4 [29, 67, 107]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k5 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S5
  CertificateChecks.KernelCensus.LiftFi23.cs 5 [45, 88, 127]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k6 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S6
  CertificateChecks.KernelCensus.LiftFi23.cs 6 [37, 79, 123]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k7 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S7
  CertificateChecks.KernelCensus.LiftFi23.cs 7 [36, 81, 123]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k8 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S8
  CertificateChecks.KernelCensus.LiftFi23.cs 8 [43, 86, 128]
#lay_f3_cuts_v CertificateChecks.KernelCensus.LiftFi23.F3k9 3 253 16 CertificateChecks.KernelCensus.LiftFi23.S9
  CertificateChecks.KernelCensus.LiftFi23.cs 9 [45, 84, 128]

public section

namespace CertificateChecks.KernelCensus.LiftFi23

open CFSG.KC.OpsLayK CFSG.KC.OpsV4 CFSG.SectionRank.Native CFSG.KC.OpsLayF3
open CFSG.KD.LC.F3.Fi23 (lay lay_ok)

@[expose] noncomputable def ch431003_ (k : Nat) : Bool :=
  chunkV CFSG.KD.LC.F3.Fi23.lay (cs.getD k (0, [], [])) (SL.getD k []) (SL.getD (k + 1) [])

theorem f3good : Good lay 16 := ⟨lay_ok, rfl, by decide, by decide⟩

theorem f3p0_0 :
    runV (ctxOf lay 16) ((((cs.getD 0 (0, [], [])).2.1.map opOf).drop 0).take (60 - 0))
      (gL lay 16 (padR lay (SL.getD 0 []) (cs.getD 0 (0, [], [])).1))
      (fun R => eqVL R F3k0.M1) = true := by quickRfl

theorem f3p0_1 :
    runV (ctxOf lay 16) ((((cs.getD 0 (0, [], [])).2.1.map opOf).drop 60).take (120 - 60))
      F3k0.M1
      (fun R => eqVL R F3k0.M2) = true := by quickRfl

theorem f3p0_2 :
    runV (ctxOf lay 16) (((cs.getD 0 (0, [], [])).2.1.map opOf).drop 120)
      F3k0.M2
      (fun R => eqVL ((cs.getD 0 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (0 + 1) []))) = true := by quickRfl

theorem f3v0 : (allValid lay (SL.getD 0 []) && allValid lay (SL.getD (0 + 1) [])) = true := by
  quickRfl

theorem ch431003_0 : ch431003_ (nat_lit 0) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v0
    (runV_split (by decide) f3p0_0
      (runV_split (by decide) f3p0_1
      f3p0_2)))

theorem f3p1_0 :
    runV (ctxOf lay 16) ((((cs.getD 1 (0, [], [])).2.1.map opOf).drop 0).take (60 - 0))
      (gL lay 16 (padR lay (SL.getD 1 []) (cs.getD 1 (0, [], [])).1))
      (fun R => eqVL R F3k1.M1) = true := by quickRfl

theorem f3p1_1 :
    runV (ctxOf lay 16) ((((cs.getD 1 (0, [], [])).2.1.map opOf).drop 60).take (120 - 60))
      F3k1.M1
      (fun R => eqVL R F3k1.M2) = true := by quickRfl

theorem f3p1_2 :
    runV (ctxOf lay 16) (((cs.getD 1 (0, [], [])).2.1.map opOf).drop 120)
      F3k1.M2
      (fun R => eqVL ((cs.getD 1 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (1 + 1) []))) = true := by quickRfl

theorem f3v1 : (allValid lay (SL.getD 1 []) && allValid lay (SL.getD (1 + 1) [])) = true := by
  quickRfl

theorem ch431003_1 : ch431003_ (nat_lit 1) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v1
    (runV_split (by decide) f3p1_0
      (runV_split (by decide) f3p1_1
      f3p1_2)))

theorem f3p2_0 :
    runV (ctxOf lay 16) ((((cs.getD 2 (0, [], [])).2.1.map opOf).drop 0).take (38 - 0))
      (gL lay 16 (padR lay (SL.getD 2 []) (cs.getD 2 (0, [], [])).1))
      (fun R => eqVL R F3k2.M1) = true := by quickRfl

theorem f3p2_1 :
    runV (ctxOf lay 16) ((((cs.getD 2 (0, [], [])).2.1.map opOf).drop 38).take (75 - 38))
      F3k2.M1
      (fun R => eqVL R F3k2.M2) = true := by quickRfl

theorem f3p2_2 :
    runV (ctxOf lay 16) ((((cs.getD 2 (0, [], [])).2.1.map opOf).drop 75).take (111 - 75))
      F3k2.M2
      (fun R => eqVL R F3k2.M3) = true := by quickRfl

theorem f3p2_3 :
    runV (ctxOf lay 16) ((((cs.getD 2 (0, [], [])).2.1.map opOf).drop 111).take (147 - 111))
      F3k2.M3
      (fun R => eqVL R F3k2.M4) = true := by quickRfl

theorem f3p2_4 :
    runV (ctxOf lay 16) (((cs.getD 2 (0, [], [])).2.1.map opOf).drop 147)
      F3k2.M4
      (fun R => eqVL ((cs.getD 2 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (2 + 1) []))) = true := by quickRfl

theorem f3v2 : (allValid lay (SL.getD 2 []) && allValid lay (SL.getD (2 + 1) [])) = true := by
  quickRfl

theorem ch431003_2 : ch431003_ (nat_lit 2) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v2
    (runV_split (by decide) f3p2_0
      (runV_split (by decide) f3p2_1
      (runV_split (by decide) f3p2_2
      (runV_split (by decide) f3p2_3
      f3p2_4)))))

theorem f3p3_0 :
    runV (ctxOf lay 16) ((((cs.getD 3 (0, [], [])).2.1.map opOf).drop 0).take (34 - 0))
      (gL lay 16 (padR lay (SL.getD 3 []) (cs.getD 3 (0, [], [])).1))
      (fun R => eqVL R F3k3.M1) = true := by quickRfl

theorem f3p3_1 :
    runV (ctxOf lay 16) ((((cs.getD 3 (0, [], [])).2.1.map opOf).drop 34).take (67 - 34))
      F3k3.M1
      (fun R => eqVL R F3k3.M2) = true := by quickRfl

theorem f3p3_2 :
    runV (ctxOf lay 16) ((((cs.getD 3 (0, [], [])).2.1.map opOf).drop 67).take (98 - 67))
      F3k3.M2
      (fun R => eqVL R F3k3.M3) = true := by quickRfl

theorem f3p3_3 :
    runV (ctxOf lay 16) ((((cs.getD 3 (0, [], [])).2.1.map opOf).drop 98).take (132 - 98))
      F3k3.M3
      (fun R => eqVL R F3k3.M4) = true := by quickRfl

theorem f3p3_4 :
    runV (ctxOf lay 16) (((cs.getD 3 (0, [], [])).2.1.map opOf).drop 132)
      F3k3.M4
      (fun R => eqVL ((cs.getD 3 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (3 + 1) []))) = true := by quickRfl

theorem f3v3 : (allValid lay (SL.getD 3 []) && allValid lay (SL.getD (3 + 1) [])) = true := by
  quickRfl

theorem ch431003_3 : ch431003_ (nat_lit 3) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v3
    (runV_split (by decide) f3p3_0
      (runV_split (by decide) f3p3_1
      (runV_split (by decide) f3p3_2
      (runV_split (by decide) f3p3_3
      f3p3_4)))))

theorem f3p4_0 :
    runV (ctxOf lay 16) ((((cs.getD 4 (0, [], [])).2.1.map opOf).drop 0).take (29 - 0))
      (gL lay 16 (padR lay (SL.getD 4 []) (cs.getD 4 (0, [], [])).1))
      (fun R => eqVL R F3k4.M1) = true := by quickRfl

theorem f3p4_1 :
    runV (ctxOf lay 16) ((((cs.getD 4 (0, [], [])).2.1.map opOf).drop 29).take (67 - 29))
      F3k4.M1
      (fun R => eqVL R F3k4.M2) = true := by quickRfl

theorem f3p4_2 :
    runV (ctxOf lay 16) ((((cs.getD 4 (0, [], [])).2.1.map opOf).drop 67).take (107 - 67))
      F3k4.M2
      (fun R => eqVL R F3k4.M3) = true := by quickRfl

theorem f3p4_3 :
    runV (ctxOf lay 16) (((cs.getD 4 (0, [], [])).2.1.map opOf).drop 107)
      F3k4.M3
      (fun R => eqVL ((cs.getD 4 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (4 + 1) []))) = true := by quickRfl

theorem f3v4 : (allValid lay (SL.getD 4 []) && allValid lay (SL.getD (4 + 1) [])) = true := by
  quickRfl

theorem ch431003_4 : ch431003_ (nat_lit 4) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v4
    (runV_split (by decide) f3p4_0
      (runV_split (by decide) f3p4_1
      (runV_split (by decide) f3p4_2
      f3p4_3))))

theorem f3p5_0 :
    runV (ctxOf lay 16) ((((cs.getD 5 (0, [], [])).2.1.map opOf).drop 0).take (45 - 0))
      (gL lay 16 (padR lay (SL.getD 5 []) (cs.getD 5 (0, [], [])).1))
      (fun R => eqVL R F3k5.M1) = true := by quickRfl

theorem f3p5_1 :
    runV (ctxOf lay 16) ((((cs.getD 5 (0, [], [])).2.1.map opOf).drop 45).take (88 - 45))
      F3k5.M1
      (fun R => eqVL R F3k5.M2) = true := by quickRfl

theorem f3p5_2 :
    runV (ctxOf lay 16) ((((cs.getD 5 (0, [], [])).2.1.map opOf).drop 88).take (127 - 88))
      F3k5.M2
      (fun R => eqVL R F3k5.M3) = true := by quickRfl

theorem f3p5_3 :
    runV (ctxOf lay 16) (((cs.getD 5 (0, [], [])).2.1.map opOf).drop 127)
      F3k5.M3
      (fun R => eqVL ((cs.getD 5 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (5 + 1) []))) = true := by quickRfl

theorem f3v5 : (allValid lay (SL.getD 5 []) && allValid lay (SL.getD (5 + 1) [])) = true := by
  quickRfl

theorem ch431003_5 : ch431003_ (nat_lit 5) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v5
    (runV_split (by decide) f3p5_0
      (runV_split (by decide) f3p5_1
      (runV_split (by decide) f3p5_2
      f3p5_3))))

theorem f3p6_0 :
    runV (ctxOf lay 16) ((((cs.getD 6 (0, [], [])).2.1.map opOf).drop 0).take (37 - 0))
      (gL lay 16 (padR lay (SL.getD 6 []) (cs.getD 6 (0, [], [])).1))
      (fun R => eqVL R F3k6.M1) = true := by quickRfl

theorem f3p6_1 :
    runV (ctxOf lay 16) ((((cs.getD 6 (0, [], [])).2.1.map opOf).drop 37).take (79 - 37))
      F3k6.M1
      (fun R => eqVL R F3k6.M2) = true := by quickRfl

theorem f3p6_2 :
    runV (ctxOf lay 16) ((((cs.getD 6 (0, [], [])).2.1.map opOf).drop 79).take (123 - 79))
      F3k6.M2
      (fun R => eqVL R F3k6.M3) = true := by quickRfl

theorem f3p6_3 :
    runV (ctxOf lay 16) (((cs.getD 6 (0, [], [])).2.1.map opOf).drop 123)
      F3k6.M3
      (fun R => eqVL ((cs.getD 6 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (6 + 1) []))) = true := by quickRfl

theorem f3v6 : (allValid lay (SL.getD 6 []) && allValid lay (SL.getD (6 + 1) [])) = true := by
  quickRfl

theorem ch431003_6 : ch431003_ (nat_lit 6) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v6
    (runV_split (by decide) f3p6_0
      (runV_split (by decide) f3p6_1
      (runV_split (by decide) f3p6_2
      f3p6_3))))

theorem f3p7_0 :
    runV (ctxOf lay 16) ((((cs.getD 7 (0, [], [])).2.1.map opOf).drop 0).take (36 - 0))
      (gL lay 16 (padR lay (SL.getD 7 []) (cs.getD 7 (0, [], [])).1))
      (fun R => eqVL R F3k7.M1) = true := by quickRfl

theorem f3p7_1 :
    runV (ctxOf lay 16) ((((cs.getD 7 (0, [], [])).2.1.map opOf).drop 36).take (81 - 36))
      F3k7.M1
      (fun R => eqVL R F3k7.M2) = true := by quickRfl

theorem f3p7_2 :
    runV (ctxOf lay 16) ((((cs.getD 7 (0, [], [])).2.1.map opOf).drop 81).take (123 - 81))
      F3k7.M2
      (fun R => eqVL R F3k7.M3) = true := by quickRfl

theorem f3p7_3 :
    runV (ctxOf lay 16) (((cs.getD 7 (0, [], [])).2.1.map opOf).drop 123)
      F3k7.M3
      (fun R => eqVL ((cs.getD 7 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (7 + 1) []))) = true := by quickRfl

theorem f3v7 : (allValid lay (SL.getD 7 []) && allValid lay (SL.getD (7 + 1) [])) = true := by
  quickRfl

theorem ch431003_7 : ch431003_ (nat_lit 7) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v7
    (runV_split (by decide) f3p7_0
      (runV_split (by decide) f3p7_1
      (runV_split (by decide) f3p7_2
      f3p7_3))))

theorem f3p8_0 :
    runV (ctxOf lay 16) ((((cs.getD 8 (0, [], [])).2.1.map opOf).drop 0).take (43 - 0))
      (gL lay 16 (padR lay (SL.getD 8 []) (cs.getD 8 (0, [], [])).1))
      (fun R => eqVL R F3k8.M1) = true := by quickRfl

theorem f3p8_1 :
    runV (ctxOf lay 16) ((((cs.getD 8 (0, [], [])).2.1.map opOf).drop 43).take (86 - 43))
      F3k8.M1
      (fun R => eqVL R F3k8.M2) = true := by quickRfl

theorem f3p8_2 :
    runV (ctxOf lay 16) ((((cs.getD 8 (0, [], [])).2.1.map opOf).drop 86).take (128 - 86))
      F3k8.M2
      (fun R => eqVL R F3k8.M3) = true := by quickRfl

theorem f3p8_3 :
    runV (ctxOf lay 16) (((cs.getD 8 (0, [], [])).2.1.map opOf).drop 128)
      F3k8.M3
      (fun R => eqVL ((cs.getD 8 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (8 + 1) []))) = true := by quickRfl

theorem f3v8 : (allValid lay (SL.getD 8 []) && allValid lay (SL.getD (8 + 1) [])) = true := by
  quickRfl

theorem ch431003_8 : ch431003_ (nat_lit 8) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v8
    (runV_split (by decide) f3p8_0
      (runV_split (by decide) f3p8_1
      (runV_split (by decide) f3p8_2
      f3p8_3))))

theorem f3p9_0 :
    runV (ctxOf lay 16) ((((cs.getD 9 (0, [], [])).2.1.map opOf).drop 0).take (45 - 0))
      (gL lay 16 (padR lay (SL.getD 9 []) (cs.getD 9 (0, [], [])).1))
      (fun R => eqVL R F3k9.M1) = true := by quickRfl

theorem f3p9_1 :
    runV (ctxOf lay 16) ((((cs.getD 9 (0, [], [])).2.1.map opOf).drop 45).take (84 - 45))
      F3k9.M1
      (fun R => eqVL R F3k9.M2) = true := by quickRfl

theorem f3p9_2 :
    runV (ctxOf lay 16) ((((cs.getD 9 (0, [], [])).2.1.map opOf).drop 84).take (128 - 84))
      F3k9.M2
      (fun R => eqVL R F3k9.M3) = true := by quickRfl

theorem f3p9_3 :
    runV (ctxOf lay 16) (((cs.getD 9 (0, [], [])).2.1.map opOf).drop 128)
      F3k9.M3
      (fun R => eqVL ((cs.getD 9 (0, [], [])).2.2.map (getV (ctxOf lay 16) R))
        (gL lay 16 (SL.getD (9 + 1) []))) = true := by quickRfl

theorem f3v9 : (allValid lay (SL.getD 9 []) && allValid lay (SL.getD (9 + 1) [])) = true := by
  quickRfl

theorem ch431003_9 : ch431003_ (nat_lit 9) = true :=
  chunkV_of_F3 f3good (chunkV3_intro f3v9
    (runV_split (by decide) f3p9_0
      (runV_split (by decide) f3p9_1
      (runV_split (by decide) f3p9_2
      f3p9_3))))

theorem pre_K : liftPreL CFSG.KD.LC.F3.Fi23.lay fi23Lift = true := by quickRfl

theorem ren_K : renOK (regsL fi23Lift) fi23Lift.base.prog cs = true := by quickRfl

theorem len_K : cs.length = 10 := by decide +kernel

theorem fin_K : liftFinL CFSG.KD.LC.F3.Fi23.lay (SL.getD cs.length []) fi23Lift = true := by
  quickRfl

end CertificateChecks.KernelCensus.LiftFi23

end

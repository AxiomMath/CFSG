module

public import Certificates.Data.Kernel.AS91K468.K46C
public import Certificates.Kernel.AS91K468.Data46
public import Certificates.Kernel.AS91K468.Data46F
public import Certificates.Kernel.AS91K468.Data46C
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

noncomputable section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAS91K468

open Certificates.Kernel.AS91K468 Certificates.Kernel.HJ12K CFSG.KD.AS91K46 CFSG.KD.AS91K46F
  CFSG.KD.AS91K46C

noncomputable abbrev fk (k : ℕ) : List ℕ := frL.getD k []

noncomputable abbrev ck (k : ℕ) : List (List ℕ) := cL.getD k []

noncomputable abbrev dk (k : ℕ) : List ℕ := dL.getD k []

theorem ch89406_f0 : (fk 0 == [fullM]) = true := by quickRfl

#kc_each CertificateChecks.KernelAS91K468 ch89406_q0_
  (fun i => chunkW pfL 20 (fk 0) (fk 0) (fk 1) (ck 0) (dk 0) i) 0 1

#kc_each CertificateChecks.KernelAS91K468 ch89406_q1_
  (fun i => chunkW pfL 20 (fk 1) (fk 1 ++ fk 0) (fk 2) (ck 1) (dk 1) i) 0 6

#kc_each CertificateChecks.KernelAS91K468 ch89406_q2_
  (fun i => chunkW pfL 20 (fk 2) (fk 2 ++ (fk 1 ++ fk 0)) (fk 3) (ck 2) (dk 2) i) 0 19

#kc_each CertificateChecks.KernelAS91K468 ch89406_q3_
  (fun i => chunkW pfL 20 (fk 3) (fk 3 ++ (fk 2 ++ (fk 1 ++ fk 0))) (fk 4) (ck 3) (dk 3) i) 0 8

#kc_each CertificateChecks.KernelAS91K468 ch89406_q4_
  (fun i => chunkW pfL 20 (fk 4) (fk 4 ++ (fk 3 ++ (fk 2 ++ (fk 1 ++ fk 0)))) [] (ck 4) (dk 4) i)
  0 1

theorem ch89406_e0 : (chunksEnd 20 1 (fk 0) (fk 0) (fk 1) (dk 0) && !(fk 1).isEmpty) = true := by
  quickRfl

theorem ch89406_e1 :
    (chunksEnd 20 6 (fk 1) (fk 1 ++ fk 0) (fk 2) (dk 1) && !(fk 2).isEmpty) = true := by
  quickRfl

theorem ch89406_e2 :
    (chunksEnd 20 19 (fk 2) (fk 2 ++ (fk 1 ++ fk 0)) (fk 3) (dk 2) && !(fk 3).isEmpty) = true := by
  quickRfl

theorem ch89406_e3 : (chunksEnd 20 8 (fk 3) (fk 3 ++ (fk 2 ++ (fk 1 ++ fk 0))) (fk 4) (dk 3) &&
    !(fk 4).isEmpty) = true := by
  quickRfl

theorem ch89406_e4 :
    chunksEnd 20 1 (fk 4) (fk 4 ++ (fk 3 ++ (fk 2 ++ (fk 1 ++ fk 0)))) [] (dk 4) = true := by
  quickRfl

theorem ch89406_q_neg :
    (!chunkW pfL 20 (fk 0) (fk 0) (fk 1) ((ck 0).map (List.map Nat.succ)) (dk 0) 0) = true := by
  quickRfl

theorem ch89406_e_neg : (!chunksEnd 20 1 (fk 0) (fk 0) (fk 0) [1, 0]) = true := by quickRfl

end CertificateChecks.KernelAS91K468

end

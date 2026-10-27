module

public import Certificates.Kernel.AxisPlane.Cover.Mats
public import Certificates.Kernel.AxisPlane.Cover.WordsOf
public import Certificates.Kernel.AxisPlane.Cover.Data

public section

namespace CertificateChecks.KernelAP.Cover

open CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Cert CFSG.Monster.AxisCount.Native

#kc_words CertificateChecks.KernelAP.Cover.H0 CertificateChecks.KernelAP.Cover.Mats pl orbit0
  with UA UB h

theorem words0 : (Cover.wordRows (UA 0) == rowsA0.toArray && Cover.wordRows (UB 0) == rowsB0.toArray &&
    ((UA 0).all Gen.isVis && (UB 0).all Gen.isVis && (List.range (nW 0)).all fun r =>
      (hW 0 r).all Gen.isVis && Cover.l2Word (hW 0 r) (lamW 0 r) == 63)) = true :=
  words_of (d := orbit0) rfl H0.UA H0.UB H0.h (by decide +kernel)

theorem lams0_eq : (List.range (nW 0)).map (lamW 0) = lams0 := by decide +kernel

theorem sizes0_eq : (List.range (nW 0)).map (sizeW 0) = sizes0 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H1 CertificateChecks.KernelAP.Cover.Mats pl orbit1
  with UA UB h

theorem words1 : (Cover.wordRows (UA 1) == rowsA1.toArray && Cover.wordRows (UB 1) == rowsB1.toArray &&
    ((UA 1).all Gen.isVis && (UB 1).all Gen.isVis && (List.range (nW 1)).all fun r =>
      (hW 1 r).all Gen.isVis && Cover.l2Word (hW 1 r) (lamW 1 r) == 63)) = true :=
  words_of (d := orbit1) rfl H1.UA H1.UB H1.h (by decide +kernel)

theorem lams1_eq : (List.range (nW 1)).map (lamW 1) = lams1 := by decide +kernel

theorem sizes1_eq : (List.range (nW 1)).map (sizeW 1) = sizes1 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H2 CertificateChecks.KernelAP.Cover.Mats pl orbit2
  with UA UB h

theorem words2 : (Cover.wordRows (UA 2) == rowsA2.toArray && Cover.wordRows (UB 2) == rowsB2.toArray &&
    ((UA 2).all Gen.isVis && (UB 2).all Gen.isVis && (List.range (nW 2)).all fun r =>
      (hW 2 r).all Gen.isVis && Cover.l2Word (hW 2 r) (lamW 2 r) == 63)) = true :=
  words_of (d := orbit2) rfl H2.UA H2.UB H2.h (by decide +kernel)

theorem lams2_eq : (List.range (nW 2)).map (lamW 2) = lams2 := by decide +kernel

theorem sizes2_eq : (List.range (nW 2)).map (sizeW 2) = sizes2 := by decide +kernel

end CertificateChecks.KernelAP.Cover

end

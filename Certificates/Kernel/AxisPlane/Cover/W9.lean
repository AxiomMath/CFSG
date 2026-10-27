module

public import Certificates.Kernel.AxisPlane.Cover.Mats
public import Certificates.Kernel.AxisPlane.Cover.WordsOf
public import Certificates.Kernel.AxisPlane.Cover.Data

public section

namespace CertificateChecks.KernelAP.Cover

open CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Cert CFSG.Monster.AxisCount.Native

#kc_words CertificateChecks.KernelAP.Cover.H9 CertificateChecks.KernelAP.Cover.Mats pl orbit9
  with UA UB h

theorem words9 : (Cover.wordRows (UA 9) == rowsA9.toArray && Cover.wordRows (UB 9) == rowsB9.toArray &&
    ((UA 9).all Gen.isVis && (UB 9).all Gen.isVis && (List.range (nW 9)).all fun r =>
      (hW 9 r).all Gen.isVis && Cover.l2Word (hW 9 r) (lamW 9 r) == 63)) = true :=
  words_of (d := orbit9) rfl H9.UA H9.UB H9.h (by decide +kernel)

theorem lams9_eq : (List.range (nW 9)).map (lamW 9) = lams9 := by decide +kernel

theorem sizes9_eq : (List.range (nW 9)).map (sizeW 9) = sizes9 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H10 CertificateChecks.KernelAP.Cover.Mats pl orbit10
  with UA UB h

theorem words10 : (Cover.wordRows (UA 10) == rowsA10.toArray &&
    Cover.wordRows (UB 10) == rowsB10.toArray &&
    ((UA 10).all Gen.isVis && (UB 10).all Gen.isVis && (List.range (nW 10)).all fun r =>
      (hW 10 r).all Gen.isVis && Cover.l2Word (hW 10 r) (lamW 10 r) == 63)) = true :=
  words_of (d := orbit10) rfl H10.UA H10.UB H10.h (by decide +kernel)

theorem lams10_eq : (List.range (nW 10)).map (lamW 10) = lams10 := by decide +kernel

theorem sizes10_eq : (List.range (nW 10)).map (sizeW 10) = sizes10 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H11 CertificateChecks.KernelAP.Cover.Mats pl orbit11
  with UA UB h

theorem words11 : (Cover.wordRows (UA 11) == rowsA11.toArray &&
    Cover.wordRows (UB 11) == rowsB11.toArray &&
    ((UA 11).all Gen.isVis && (UB 11).all Gen.isVis && (List.range (nW 11)).all fun r =>
      (hW 11 r).all Gen.isVis && Cover.l2Word (hW 11 r) (lamW 11 r) == 63)) = true :=
  words_of (d := orbit11) rfl H11.UA H11.UB H11.h (by decide +kernel)

theorem lams11_eq : (List.range (nW 11)).map (lamW 11) = lams11 := by decide +kernel

theorem sizes11_eq : (List.range (nW 11)).map (sizeW 11) = sizes11 := by decide +kernel

end CertificateChecks.KernelAP.Cover

end

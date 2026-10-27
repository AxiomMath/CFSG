module

public import Certificates.Kernel.AxisPlane.Cover.Mats
public import Certificates.Kernel.AxisPlane.Cover.WordsOf
public import Certificates.Kernel.AxisPlane.Cover.Data

public section

namespace CertificateChecks.KernelAP.Cover

open CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Cert CFSG.Monster.AxisCount.Native

#kc_words CertificateChecks.KernelAP.Cover.H6 CertificateChecks.KernelAP.Cover.Mats pl orbit6
  with UA UB h

theorem words6 : (Cover.wordRows (UA 6) == rowsA6.toArray && Cover.wordRows (UB 6) == rowsB6.toArray &&
    ((UA 6).all Gen.isVis && (UB 6).all Gen.isVis && (List.range (nW 6)).all fun r =>
      (hW 6 r).all Gen.isVis && Cover.l2Word (hW 6 r) (lamW 6 r) == 63)) = true :=
  words_of (d := orbit6) rfl H6.UA H6.UB H6.h (by decide +kernel)

theorem lams6_eq : (List.range (nW 6)).map (lamW 6) = lams6 := by decide +kernel

theorem sizes6_eq : (List.range (nW 6)).map (sizeW 6) = sizes6 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H7 CertificateChecks.KernelAP.Cover.Mats pl orbit7
  with UA UB h

theorem words7 : (Cover.wordRows (UA 7) == rowsA7.toArray && Cover.wordRows (UB 7) == rowsB7.toArray &&
    ((UA 7).all Gen.isVis && (UB 7).all Gen.isVis && (List.range (nW 7)).all fun r =>
      (hW 7 r).all Gen.isVis && Cover.l2Word (hW 7 r) (lamW 7 r) == 63)) = true :=
  words_of (d := orbit7) rfl H7.UA H7.UB H7.h (by decide +kernel)

theorem lams7_eq : (List.range (nW 7)).map (lamW 7) = lams7 := by decide +kernel

theorem sizes7_eq : (List.range (nW 7)).map (sizeW 7) = sizes7 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H8 CertificateChecks.KernelAP.Cover.Mats pl orbit8
  with UA UB h

theorem words8 : (Cover.wordRows (UA 8) == rowsA8.toArray && Cover.wordRows (UB 8) == rowsB8.toArray &&
    ((UA 8).all Gen.isVis && (UB 8).all Gen.isVis && (List.range (nW 8)).all fun r =>
      (hW 8 r).all Gen.isVis && Cover.l2Word (hW 8 r) (lamW 8 r) == 63)) = true :=
  words_of (d := orbit8) rfl H8.UA H8.UB H8.h (by decide +kernel)

theorem lams8_eq : (List.range (nW 8)).map (lamW 8) = lams8 := by decide +kernel

theorem sizes8_eq : (List.range (nW 8)).map (sizeW 8) = sizes8 := by decide +kernel

end CertificateChecks.KernelAP.Cover

end

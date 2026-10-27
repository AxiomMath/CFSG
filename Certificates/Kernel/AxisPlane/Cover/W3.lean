module

public import Certificates.Kernel.AxisPlane.Cover.Mats
public import Certificates.Kernel.AxisPlane.Cover.WordsOf
public import Certificates.Kernel.AxisPlane.Cover.Data

public section

namespace CertificateChecks.KernelAP.Cover

open CFSG.Monster.AxisCount CFSG.Monster.AxisCount.Cert CFSG.Monster.AxisCount.Native

#kc_words CertificateChecks.KernelAP.Cover.H3 CertificateChecks.KernelAP.Cover.Mats pl orbit3
  with UA UB h

theorem words3 : (Cover.wordRows (UA 3) == rowsA3.toArray && Cover.wordRows (UB 3) == rowsB3.toArray &&
    ((UA 3).all Gen.isVis && (UB 3).all Gen.isVis && (List.range (nW 3)).all fun r =>
      (hW 3 r).all Gen.isVis && Cover.l2Word (hW 3 r) (lamW 3 r) == 63)) = true :=
  words_of (d := orbit3) rfl H3.UA H3.UB H3.h (by decide +kernel)

theorem lams3_eq : (List.range (nW 3)).map (lamW 3) = lams3 := by decide +kernel

theorem sizes3_eq : (List.range (nW 3)).map (sizeW 3) = sizes3 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H4 CertificateChecks.KernelAP.Cover.Mats pl orbit4
  with UA UB h

theorem words4 : (Cover.wordRows (UA 4) == rowsA4.toArray && Cover.wordRows (UB 4) == rowsB4.toArray &&
    ((UA 4).all Gen.isVis && (UB 4).all Gen.isVis && (List.range (nW 4)).all fun r =>
      (hW 4 r).all Gen.isVis && Cover.l2Word (hW 4 r) (lamW 4 r) == 63)) = true :=
  words_of (d := orbit4) rfl H4.UA H4.UB H4.h (by decide +kernel)

theorem lams4_eq : (List.range (nW 4)).map (lamW 4) = lams4 := by decide +kernel

theorem sizes4_eq : (List.range (nW 4)).map (sizeW 4) = sizes4 := by decide +kernel

#kc_words CertificateChecks.KernelAP.Cover.H5 CertificateChecks.KernelAP.Cover.Mats pl orbit5
  with UA UB h

theorem words5 : (Cover.wordRows (UA 5) == rowsA5.toArray && Cover.wordRows (UB 5) == rowsB5.toArray &&
    ((UA 5).all Gen.isVis && (UB 5).all Gen.isVis && (List.range (nW 5)).all fun r =>
      (hW 5 r).all Gen.isVis && Cover.l2Word (hW 5 r) (lamW 5 r) == 63)) = true :=
  words_of (d := orbit5) rfl H5.UA H5.UB H5.h (by decide +kernel)

theorem lams5_eq : (List.range (nW 5)).map (lamW 5) = lams5 := by decide +kernel

theorem sizes5_eq : (List.range (nW 5)).map (sizeW 5) = sizes5 := by decide +kernel

end CertificateChecks.KernelAP.Cover

end

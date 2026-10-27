module

public import Certificates.Kernel.AxisPlane.Baby.Mats
public import Certificates.Kernel.AxisPlane.Baby.WordsOf
public import Certificates.Kernel.AxisPlane.Baby.Data

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.Monster.AxisCount.Baby

#kc_words CertificateChecks.KernelAP.Baby.H5 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit5
  with U h

theorem words5 :
    rowsB babyOrbit5 = ([rows5_0, rows5_1, rows5_2, rows5_3].map List.toArray).toArray ∧
    wordsB babyOrbit5 = true :=
  words_of H5.U H5.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H6 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit6
  with U h

theorem words6 :
    rowsB babyOrbit6 = ([rows6_0, rows6_1, rows6_2, rows6_3].map List.toArray).toArray ∧
    wordsB babyOrbit6 = true :=
  words_of H6.U H6.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H7 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit7
  with U h

theorem words7 :
    rowsB babyOrbit7 = ([rows7_0, rows7_1, rows7_2, rows7_3].map List.toArray).toArray ∧
    wordsB babyOrbit7 = true :=
  words_of H7.U H7.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H8 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit8
  with U h

theorem words8 :
    rowsB babyOrbit8 = ([rows8_0, rows8_1, rows8_2, rows8_3].map List.toArray).toArray ∧
    wordsB babyOrbit8 = true :=
  words_of H8.U H8.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H9 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit9
  with U h

theorem words9 :
    rowsB babyOrbit9 = ([rows9_0, rows9_1, rows9_2, rows9_3].map List.toArray).toArray ∧
    wordsB babyOrbit9 = true :=
  words_of H9.U H9.h (by decide +kernel)

end CertificateChecks.KernelAP.Baby

end

module

public import Certificates.Kernel.AxisPlane.Baby.Mats
public import Certificates.Kernel.AxisPlane.Baby.WordsOf
public import Certificates.Kernel.AxisPlane.Baby.Data

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.Monster.AxisCount.Baby

#kc_words CertificateChecks.KernelAP.Baby.H0 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit0
  with U h

theorem words0 :
    rowsB babyOrbit0 = ([rows0_0, rows0_1, rows0_2, rows0_3].map List.toArray).toArray ∧
    wordsB babyOrbit0 = true :=
  words_of H0.U H0.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H1 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit1
  with U h

theorem words1 :
    rowsB babyOrbit1 = ([rows1_0, rows1_1, rows1_2, rows1_3].map List.toArray).toArray ∧
    wordsB babyOrbit1 = true :=
  words_of H1.U H1.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H2 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit2
  with U h

theorem words2 :
    rowsB babyOrbit2 = ([rows2_0, rows2_1, rows2_2, rows2_3].map List.toArray).toArray ∧
    wordsB babyOrbit2 = true :=
  words_of H2.U H2.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H3 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit3
  with U h

theorem words3 :
    rowsB babyOrbit3 = ([rows3_0, rows3_1, rows3_2, rows3_3].map List.toArray).toArray ∧
    wordsB babyOrbit3 = true :=
  words_of H3.U H3.h (by decide +kernel)

#kc_words CertificateChecks.KernelAP.Baby.H4 CertificateChecks.KernelAP.Baby.Mats bpl babyOrbit4
  with U h

theorem words4 :
    rowsB babyOrbit4 = ([rows4_0, rows4_1, rows4_2, rows4_3].map List.toArray).toArray ∧
    wordsB babyOrbit4 = true :=
  words_of H4.U H4.h (by decide +kernel)

end CertificateChecks.KernelAP.Baby

end


module


public import Certificates.Certificate10073

public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative Matrix

theorem validOK_true : validOK = true :=
  Certificates.certificate10073.1

theorem fixOK_true : fixOK = true :=
  Certificates.certificate10073.2.1

theorem partnerOK_true : partnerOK = true :=
  Certificates.certificate10073.2.2.1

theorem conjOK_true : conjOK = true :=
  Certificates.certificate10073.2.2.2.1

theorem fixOK₂_true : fixOK₂ = true :=
  Certificates.certificate10073.2.2.2.2.1

theorem pairFixOK_0 : pairFixOK 0 1024 405 = true :=
  Certificates.certificate10073.2.2.2.2.2.1

theorem pairFixOK_1 : pairFixOK 1 256 135 = true :=
  Certificates.certificate10073.2.2.2.2.2.2.1

theorem pairFixOK_2 : pairFixOK 2 256 75 = true :=
  Certificates.certificate10073.2.2.2.2.2.2.2.1

theorem gramOK_1 :
    gramOK (transposeRows 24 f0Rows) (Wk 1) = true :=
  Certificates.certificate10073.2.2.2.2.2.2.2.2.1

theorem gramOK_2 :
    gramOK (transposeRows 24 f0Rows) (Wk 2) = true :=
  Certificates.certificate10073.2.2.2.2.2.2.2.2.2.1

theorem lit_ok : ∃ W : OddW, OddOK W :=
  Certificates.certificate10073.2.2.2.2.2.2.2.2.2.2

end CFSG.Sporadic.Co1.Module.Odd

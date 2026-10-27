module

public import CFSG.Sporadic.J4.QT2LocCntNative
public meta import CFSG.Sporadic.J4.QT2LocCntNative
public import Certificates.Certificate4010

public section

namespace CFSG.Sporadic.J4.QT2

theorem mask_cover : ∀ c < 2048, c = 0 ∨ c ∈ tMasks ∨ c ∈ zMasks :=
  Certificates.certificate4010

end CFSG.Sporadic.J4.QT2

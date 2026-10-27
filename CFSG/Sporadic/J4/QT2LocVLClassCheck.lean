module

public import Certificates.Certificate4012

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4.Native

theorem vlAll_size_eq : vlAll.size = 149 :=
  Certificates.certificate4012.1

theorem vlAll_sizes : ∀ g < 149, vlAll[g]!.size = 16 :=
  Certificates.certificate4012.2.1

theorem vlClass_wit : ∀ g < 149, ∃ r ∈ vlRepIdx, ∃ c < 6720,
    vlConjEq r g c = true ∧ eqRows (mulRows vlCx[c]! vlCxInv[c]!) idRows = true :=
  Certificates.certificate4012.2.2.1

theorem chkNamed_true : chkNamed = true :=
  Certificates.certificate4012.2.2.2

end CFSG.Sporadic.J4.QT2

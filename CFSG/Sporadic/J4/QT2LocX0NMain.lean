
module

public import CFSG.Sporadic.J4.QT2LocX0NMainBase

public import CFSG.Sporadic.J4

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix

theorem exists_conj_fiveElt_sq_J4 :
    ∃ n : J, n * fiveElt * n⁻¹ = fiveElt ^ 2 :=
  exists_conj_fiveElt_sq j4Facts.mat

end CFSG.Sporadic.J4.QT2


module

import all CFSG.Sporadic.J4.QT2LocX0CentMainBase
public import CFSG.Sporadic.J4.QT2LocX0CentMainBase1
import all CFSG.Sporadic.J4.QT2LocX0CentMainBase1

public import CFSG.Sporadic.J4.QT2LocScanCheck
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

set_option maxRecDepth 100000

theorem centralizer_fiveElt_eq (_hF : J4Facts) :
    Subgroup.centralizer ({fiveElt} : Set J) = X0Sub :=
  centralizer_fiveElt_eq_X0Sub

theorem card_centralizer_fiveElt
    (hF : J4Facts) :
    Nat.card ↥(Subgroup.centralizer ({fiveElt} : Set J)) = 6720 := by
  rw [centralizer_fiveElt_eq hF]
  exact card_X0Sub hF.mat

end CFSG.Sporadic.J4.QT2

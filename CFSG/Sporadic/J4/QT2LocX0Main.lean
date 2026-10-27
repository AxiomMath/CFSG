
module

public import CFSG.Sporadic.J4.QT2LocX0MainBase

public import CFSG.Sporadic.J4

public section

namespace CFSG.Sporadic.J4.QT2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT Matrix
open scoped Classical

theorem orderOf_fiveElt_J4 :
    orderOf fiveElt = 5 := orderOf_fiveElt j4Facts.mat

theorem card_X0Sub_J4 :
    Nat.card X0Sub = 6720 := card_X0Sub j4Facts.mat

theorem X0Sub_le_centralizer_J4 :
    X0Sub ≤ Subgroup.centralizer ({fiveElt} : Set J) :=
  X0Sub_le_centralizer j4Facts.mat

end CFSG.Sporadic.J4.QT2

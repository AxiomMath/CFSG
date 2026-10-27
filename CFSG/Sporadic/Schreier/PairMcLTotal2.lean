module

public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import CFSG.Sporadic.Schreier.PairMcLTotal2Inputs
public import Certificates.Certificate2246

public section

namespace CFSG.Sporadic.Schreier.PairMcL

open CFSG.Sporadic.Schreier.PairNative

theorem word_orders2 :
    ordB bs (patW wA wB [false, true, true]) 12 = true ∧
      ordB bs (patW wA wB [false, true, false, true, true]) 14 = true ∧
      ordB bs (patW wA wB pat10) 10 = true :=
  Certificates.certificate2246.1

theorem total2 :
    (cl.map fun c => c.2.1.size * countPair bs 5 c.1 conds2 blocks).sum = 1796256000 :=
  Certificates.certificate2246.2

end CFSG.Sporadic.Schreier.PairMcL

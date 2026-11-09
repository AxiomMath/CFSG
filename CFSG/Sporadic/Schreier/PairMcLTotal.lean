module

public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import Certificates.Certificate2245

public section

namespace CFSG.Sporadic.Schreier.PairMcL

open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates.Native CFSG.Monster.B.Co2.Native

theorem card_class :
    Nat.card {x : mclP // IsConj (⟨mclGen 0, Subgroup.subset_closure (by simp)⟩ : mclP) x} =
      22275 :=
  Certificates.certificate2245.1

theorem total : countPair bs 5 wA conds blocks = 2177280 :=
  Certificates.certificate2245.2

end CFSG.Sporadic.Schreier.PairMcL

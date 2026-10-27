module

public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairOuterPat
public import CFSG.Sporadic.Schreier.PairCounts
public meta import CFSG.Sporadic.Schreier.PairHSCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
public import Certificates.Certificate2218
public import Certificates.Certificate2219
public import Certificates.Certificate2222
public import Certificates.Certificate2220
public import Certificates.Certificate2221
public import Certificates.Certificate3167

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierAlternating

theorem HS_outer_card_le_two :
    Nat.card (Outer Blueprint.NativeSporadic.HS) ≤ 2 ∧
      IsMulCommutative (Outer Blueprint.NativeSporadic.HS) ∧
      Group.IsSolvable (Outer Blueprint.NativeSporadic.HS) := by
  have : Finite Blueprint.NativeSporadic.HS := CFSG.Sporadic.HS.fam_hs_simplicity.1
  have hcard : Nat.card (Outer Blueprint.NativeSporadic.HS) ≤ 2 :=
    Certificates.certificate2222
  exact ⟨hcard, commutative_of_card_le_four (hcard.trans (by norm_num)),
    solvable_of_card_le_four (hcard.trans (by norm_num))⟩

end CFSG.Sporadic.Schreier

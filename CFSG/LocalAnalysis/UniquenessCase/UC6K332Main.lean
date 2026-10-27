module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K332S
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332GenRow
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Glue
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Exc
import CFSG.LocalAnalysis.UniquenessCase.UC6N588A1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (GoodRow k432InnerThreeP_of_goodRow k432ListP_of_goodRow)

@[expose] def Row332 : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.IsQuasisimple L → PL332 L →
    GoodRow (L ⧸ Subgroup.center L)

theorem item332_of_row (h : Row332) : Item4_32CompP PL332 :=
  item4_32CompP_of_three PL332 (k432InnerThreeP_of_goodRow PL332 h) (k432ListP_of_goodRow PL332 h)

theorem k332S_of_row (hrow : Row332) (hexc : K332Exclusion) : K332S := by
  intro G _ _ hK S hS hrk Z hZS hZ3 hwc hd
  obtain ⟨hK', hS', hrk', hZS', hZ3', hwc', hd'⟩ := descend332 hK hS hrk hZS hZ3 hwc hd
  set N := CFSG.pPrimeCore 3 G with hN
  have hcore : CFSG.pPrimeCore 3 (G ⧸ N) = ⊥ := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact CFSG.Semidihedral.Local.pPrimeCore_quotient_self_eq_bot G 3
  have hrkT : CFSG.Open.pRank 3 (⊤ : Subgroup (G ⧸ N)) ≤ 3 :=
    (N588A.pRank_le_of_isSylowOf Nat.prime_three hS' ⊤).trans hrk'
  have hmain := item332_of_row hrow (G ⧸ N)
    (components_PL332 hK' hrkT fun K hKc =>
      Item432Proof.isPGroup_center_of_isSubnormal hcore hKc.2) hcore
    (Z.map (QuotientGroup.mk' N)) hZ3' (wc_normalizer hS' hZS' hwc')
  have hex := hexc (G ⧸ N) _ hS' _ hZS' hZ3' hwc' hd'
  have h1 : CFSG.Open.pRank 3 (Subgroup.normalClosure
      ((Z.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) = 1 := by
    rcases hmain with h | h | h
    · exact h
    · exact absurd h hex.1
    · exact absurd h hex.2
  exact pullback332 hZ3 h1

theorem k332Cyc_of_row (hrow : Row332) (hexc : K332Exclusion) : K332Cyc :=
  k332Cyc_of_k332S (k332S_of_row hrow hexc)

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

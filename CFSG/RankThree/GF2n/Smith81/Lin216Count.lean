module

import CFSG.RankThree.GF2n.Smith81.LinOddSteps
public import CFSG.RankThree.GF2n.Smith81.LinOddBasic
import CFSG.RankThree.GF2n.Smith81.Lin212ComplRoot

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

variable {G : Type} [Group G]

theorem isConj_of_inZClass [Finite G] {M Q Z A : Subgroup G}
    (H : StrothHyp M Q Z) {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (hA : IsZConjugate Z A) {s : G}
    (hs : InZClass A s) : IsConj z s := by
  obtain ⟨g, a, haA, ha1, rfl⟩ := hs
  obtain ⟨k, hk⟩ := exists_conj_of_inZClass (u := z) H ⟨1, z, hz, hz1, by group⟩
    ((inZClass_of_mem_root hA haA ha1).conj g)
  exact isConj_iff.mpr ⟨k, hk⟩

end CFSG.RankThree.GF2n.Smith81

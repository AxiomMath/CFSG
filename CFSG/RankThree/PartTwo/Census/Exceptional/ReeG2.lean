module

public import CFSG.RankThree.PartTwo.Census.Exceptional.ReeIndex
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.RankThree.PartTwo.Census.Exceptional

open TauCeti

theorem four_le_twoLocalOddRank_reeG2Index (d : ReeG2LieIndex) {m : ℕ}
    (hd : d.1.fieldExponent = 2 * m + 1) (hm : 2 ≤ m)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.twoLocalOddRank (FixedPointCandidate d.steinberg) :=
  four_le_twoLocalOddRank_of_localRank Nat.prime_three (by norm_num)
    ((by omega : 4 ≤ 2 * m + 1).trans (le_localRank_reeG2 hd (by omega)))

theorem four_le_twoLocalOddRank_reeG2 (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid) (hm : 2 ≤ m)
    [hfin : Finite (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group] :
    4 ≤ CFSG.twoLocalOddRank (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group :=
  @four_le_twoLocalOddRank_reeG2Index (ReeG2LieIndex.of m hv) m
    (LieTypeIndex.fieldExponent_reeG2 m) hm hfin

end CFSG.RankThree.PartTwo.Census.Exceptional

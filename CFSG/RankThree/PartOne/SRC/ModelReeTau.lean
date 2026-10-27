module

public import CFSG.RankThree.PartOne.SRC.ModelRee
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartTwo.Census.Exceptional


theorem rankFourCover_reeG2 (m : ℕ) (hv : (LieTypeIndex.reeG2 m).Valid) (hm : 2 ≤ m)
    [hfin : Finite (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group] :
    RankFourCover 3 (CFSGIndex.lie ⟨.reeG2 m, hv⟩).Group :=
  @rankFourCover_ree m (ReeG2LieIndex.of m hv) (LieTypeIndex.fieldExponent_reeG2 m) hm hfin

end CFSG.RankThree.PartOne.SRC

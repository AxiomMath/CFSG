module

public import CFSG.Sporadic.Bridge.J4Surj
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint TauCeti CFSG.QuasithinUnique.SQTK

theorem nonempty_mulEquiv_carrier_J4 [IsSimpleGroup SporadicName.J4.Group] :
    Nonempty (SporadicName.J4.Group ≃* NativeSporadic.J4) := by
  have : IsSimpleGroup Sporadic.j4Presentation.Group := ‹IsSimpleGroup SporadicName.J4.Group›
  have : Nontrivial CFSG.Sporadic.J4.J :=
    nontrivial_of_two_le_natCard (k := 86775571046077562880) (by norm_num)
      CFSG.Sporadic.Bridge.J4.card_J.symm.le
  exact ⟨(mulEquivOfSurjective CFSG.Sporadic.Bridge.J4.φ
    CFSG.Sporadic.Bridge.J4.φ_surjective).trans
      (CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat).symm⟩

end CFSG.RankThree.PartTwo.Census

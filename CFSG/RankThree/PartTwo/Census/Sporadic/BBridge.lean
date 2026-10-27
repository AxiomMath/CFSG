module

public import CFSG.Sporadic.Bridge.BSurj
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.SimpleTrick
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint TauCeti CFSG.QuasithinUnique.SQTK

theorem nonempty_mulEquiv_B [IsSimpleGroup SporadicName.B.Group] [Nontrivial NativeSporadic.B] :
    Nonempty (SporadicName.B.Group ≃* NativeSporadic.B) := by
  have : IsSimpleGroup CFSG.Sporadic.Bridge.B.pres.Group := ‹IsSimpleGroup SporadicName.B.Group›
  exact ⟨@mulEquivOfSurjective CFSG.Sporadic.Bridge.B.pres.Group NativeSporadic.B _
    Units.instGroup _ _ CFSG.Sporadic.Bridge.B.φ CFSG.Sporadic.Bridge.B.φ_surjective⟩

end CFSG.RankThree.PartTwo.Census

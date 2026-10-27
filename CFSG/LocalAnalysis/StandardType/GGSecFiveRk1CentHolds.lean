module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1CitedDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanProjection

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin
open scoped Pointwise commutatorElement

namespace SecFiveRk1C

private theorem bstar_le_normalizer_of_routeCfg {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) :
    Bs ≤ Subgroup.normalizer (X : Set G) := by
  rcases hX with rfl | hK
  · exact GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  · obtain ⟨y, hy⟩ := hcfg.2.2.2.1.2 X hK
    exact GGDichotomy.le_normalizer_of_innerDiagOn (hcfg.1.2.2.1.2 y X hy)

end SecFiveRk1C

theorem ggSecFiveRk1CentInput_holds :
    GGSecFiveRk1CentInput := by
  intro G _ _ _ _ Bs _ _ _ _ _ hcfg _ _ _ _ _ _ X hX _ r _ _ _ hQH hQQ hQX
  have hHB : ggHyperplane Bs r ≤ Bs := Subgroup.map_subtype_le _
  have hHN : ggHyperplane Bs r ≤ Subgroup.normalizer (X : Set G) :=
    hHB.trans (SecFiveRk1C.bstar_le_normalizer_of_routeCfg hcfg hX)
  exact (SecFiveRk1C.le_perfectCore_sup_centralizer inf_le_left hQQ
    (SecFiveRk1C.le_inf_centralizer_sup_of_perfect hHN hQH hQQ hQX)).trans
    (sup_le_sup_right (SecFiveRk1C.perfectCore_le_ggOTwoPrime _) _)

end CFSG.StandardType

end

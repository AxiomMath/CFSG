module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

theorem nonempty_bar2_hinf_map_of_injective {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] (f : G →* G') (hf : Function.Injective f) (P : Subgroup G) :
    Nonempty (Bar2 (Hinf P) ≃* Bar2 (Hinf (P.map f))) := by
  have hHinf : (Hinf P).map f = Hinf (P.map f) := Hinf_map f P
  let eSub : ↥(Hinf P) ≃* ↥(Hinf (P.map f)) :=
    ((Hinf P).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hHinf)
  exact nonempty_bar2_mulEquiv_of_equiv eSub

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD

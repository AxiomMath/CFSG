module

public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.StandardType.GGE0ChevStMarking
public import CFSG.LocalAnalysis.StandardType.GGCompFieldCatalogue
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructE6Diag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem excNoSuzukiReeE6_holds
    : ExcNoSuzukiReeE6 := by
  intro K _ _ _ p β hp hp2 hβ1 hβp hβI X hX hmark
  have hD : ∀ c, AutSt.e6DiagHom K c = rootDiagAutHom .E6 K c := fun c =>
    (KGE6.rootDiagAutHom_eq_exactNormalAut c).symm
  have hrange : (AutSt.e6DiagHom K).range = (rootDiagAutHom .E6 K).range := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, (hD c).symm⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, hD c⟩
  have hβ' : β ∈ CFSG.StandardType.LayerSixE.inndiagAut .E6 K := by
    simp only [CFSG.StandardType.LayerSixE.inndiagAut]
    rw [← hrange]
    exact hβI
  have hX' : CFSG.Open.IsComponentOf X
      (CFSG.StandardType.LayerSixE.autFix (Subgroup.zpowers β)) := by
    rw [CFSG.StandardType.LayerSixE.autFix_zpowers_eq]
    exact (CFSG.Assembly.isComponentOf_iff_open).1 hX
  exact ggChevStMarking_of_compFieldDataQ
    (ggE6CompFieldInputQ K p hp hp2 β hβ' hβp X hX') hmark

end CFSG.StandardType

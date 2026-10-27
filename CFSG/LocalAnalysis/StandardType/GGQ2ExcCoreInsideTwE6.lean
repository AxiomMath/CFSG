module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideE6
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInsideWit
public import Certificates.Certificate712574
public import Certificates.Certificate712575
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideCode
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreInside
import CFSG.LocalAnalysis.StandardType.GGQ2ExcTwE6InnerTorus
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideCodeBase
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideImg
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusInsideList

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus


theorem excCoreInside_E6_of_census {m : Fin 6} (hm : m = 2 ∨ m = 3)
    (hcen : ExcRaw.InsideCensus m) : ExcCoreInside m .E6 :=
  excCoreInside_of_insideCensus (Or.inr (Or.inl rfl)) hcen fun hS d hfl => by
    have hcard := card_fullThreeTorus_inf_Γ _ hS d.ζ_pow_three
      (orderOf_eq_prime d.ζ_pow_three d.ζ_ne_one)
    rcases hfl with ⟨-, rfl | ⟨k, rfl⟩⟩ | ⟨h5, -⟩
    · exact ggLinImage_codeComponent_univ_le_inside _ hS hcard hm d
    · exact ggLinImage_codeComponent_orthCode_le_inside _ hS hcard hm d k
    · rcases hm with rfl | rfl <;> simp at h5

theorem excCoreInside_E6_two : ExcCoreInside 2 .E6 :=
  excCoreInside_E6_of_census (Or.inl rfl) ExcRaw.insideCensus_E6_two

theorem excCoreInside_E6_three : ExcCoreInside 3 .E6 :=
  excCoreInside_E6_of_census (Or.inr rfl) ExcRaw.insideCensus_E6_three

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end

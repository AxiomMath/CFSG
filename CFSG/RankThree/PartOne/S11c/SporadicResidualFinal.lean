module

public import CFSG.RankThree.PartOne.S11c.SporadicPlaneJ2
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneHSMcL
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneHe
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneRu
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneON
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneCo2
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneCo3
public import CFSG.RankThree.PartOne.S11c.SporadicPlaneTh
public import CFSG.RankThree.PartOne.KS.NoPlane
public import CFSG.RankThree.PartOne.KP.Fi22Section
public import CFSG.RankThree.PartOne.KS.FischerSections
public import CFSG.RankThree.PartOne.KP.BExclusion
public import CFSG.RankThree.PartOne.KP.MSectionMonster
public import CFSG.RankThree.PartOne.SPOR.Final

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem sporadicPlanesCentralize_of_noPlaneAut {A : Type} [Group A] (h : NoPlaneAut A) :
    SporadicPlanesCentralize A := by
  intro T _ _ hs hnab hTA p E U hpl
  have := hs
  exfalso
  have hdvd := Subgroup.card_subgroup_dvd_card E
  rw [hpl.card] at hdvd
  exact h T hnab hTA p hpl.prime hpl.three_lt hdvd

theorem sporadicResidual_holds :
    ActualCoverSporadicMovingPlaneFiveModelResidual := by
  obtain ⟨h23, h24⟩ := sectionsForceEvenRankFour_fi23_fi24prime sectionsForceEvenRankFour_Fi22
    hasSection_fi23_fi22 hasSection_fi24prime_fi23
  exact sporadicResidual_of_inputs
    { m11 := sporadicPlanesCentralize_of_noPlaneAut noPlaneAut_M11
      m12 := sporadicPlanesCentralize_of_noPlaneAut noPlaneAut_M12
      m22 := sporadicPlanesCentralize_of_noPlaneAut noPlaneAut_M22
      m23 := sporadicPlanesCentralize_of_noPlaneAut noPlaneAut_M23
      m24 := sporadicPlanesCentralize_of_noPlaneAut noPlaneAut_M24
      j1 := sporadicPlanesCentralize_of_noPlaneAut noPlaneAut_J1
      j2 := sporadicPlanesCentralize_J2
      j3 := sporadicPlanesCentralize_of_noPlaneAut noPlaneAut_J3
      hs := sporadicPlanesCentralize_HS
      mcl := sporadicPlanesCentralize_McL
      he := sporadicPlanesCentralize_He
      ru := sporadicPlanesCentralize_Ru
      on := sporadicPlanesCentralize_ONan
      co2 := sporadicPlanesCentralize_Co2 SPOR.co2AllInner_holds
      co3 := sporadicPlanesCentralize_Co3 co3P_allInner
      th := sporadicPlanesCentralize_Th
      fi22 := sectionsForceEvenRankFour_Fi22
      fi23 := h23
      fi24 := h24
      b := sectionsForceEvenRankFour_B
      m := simplePresentationM_sections_of_B_section sectionsForceEvenRankFour_B
        simplePresentationMHasBSection_holds }

end CFSG.RankThree.PartOne

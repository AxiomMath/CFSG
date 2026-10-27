module

public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.RankThree.LocalRank
open CFSG.Blueprint.NativeSporadic (Carrier)
open scoped Pointwise

@[expose] def SporadicPlaneOdd (A : Type) [Group A] : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* A) → ∀ p : ℕ, p.Prime → 3 < p → PlaneLocalCoreOdd p T

structure SporadicSectionCases : Prop where
  fi22 : SectionsForceEvenRankFour (Carrier .Fi22)
  fi23 : SectionsForceEvenRankFour (Carrier .Fi23)
  fi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime)
  b : SectionsForceEvenRankFour (Carrier .B)
  m : SimplePresentationMSectionsForceEvenRankFour

structure SporadicPlaneCases : Prop where
  m11 : SporadicPlaneOdd (Carrier .M11)
  m12 : SporadicPlaneOdd (Carrier .M12)
  m22 : SporadicPlaneOdd (Carrier .M22)
  m23 : SporadicPlaneOdd (Carrier .M23)
  m24 : SporadicPlaneOdd (Carrier .M24)
  j1 : SporadicPlaneOdd (Carrier .J1)
  j2 : SporadicPlaneOdd (Carrier .J2)
  j3 : SporadicPlaneOdd (Carrier .J3)
  j4 : SporadicPlaneOdd (Carrier .J4)
  co1 : SporadicPlaneOdd (Carrier .Co1)
  co2 : SporadicPlaneOdd (Carrier .Co2)
  co3 : SporadicPlaneOdd (Carrier .Co3)
  hs : SporadicPlaneOdd (Carrier .HS)
  mcl : SporadicPlaneOdd (Carrier .McL)
  he : SporadicPlaneOdd (Carrier .He)
  ru : SporadicPlaneOdd (Carrier .Ru)
  suz : SporadicPlaneOdd (Carrier .Suz)
  on : SporadicPlaneOdd (Carrier .ONan)
  hn : SporadicPlaneOdd (Carrier .HN)
  ly : SporadicPlaneOdd (Carrier .Ly)
  th : SporadicPlaneOdd (Carrier .Th)

theorem original_sporadic_component_local_core_odd_action_of_cases
    (hsec : SporadicSectionCases) (hpl : SporadicPlaneCases) :
    OriginalSporadicComponentLocalCoreOddAction := by
  intro X _ _ hX p hp hp3 N _ hN E hE hEc t ht ht1 L hL hspor hEL hSL
  obtain ⟨s, ⟨e⟩⟩ := hspor
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  have hnab := hL.1.2.2
  have hp2 : p ≠ 2 := by omega
  have byPlane : SporadicPlaneOdd (Carrier s) → ComponentLocalCoreOddConclusion p E t L := by
    intro h
    have hplane : PlaneLocalCoreOdd p (L ⧸ Subgroup.center L) := h _ hnab ⟨e⟩ p hp hp3
    obtain ⟨hset, hWN, hodd, -, -⟩ :=
      component_local_core_odd_action_of_plane hp hp2 hE hEc ht ht1 hL hEL hSL hplane
    exact ⟨hset, hWN, hodd⟩
  have bySection : SectionsForceEvenRankFour (Carrier s) →
      ComponentLocalCoreOddConclusion p E t L := by
    intro h
    obtain ⟨H, K, hK, ⟨φ⟩⟩ := exists_section_of_quotient_subgroup N L
    have h4 := h X H K ⟨φ.trans e⟩
    omega
  cases s
  · exact byPlane hpl.m11
  · exact byPlane hpl.m12
  · exact byPlane hpl.m22
  · exact byPlane hpl.m23
  · exact byPlane hpl.m24
  · exact byPlane hpl.j1
  · exact byPlane hpl.j2
  · exact byPlane hpl.j3
  · exact byPlane hpl.j4
  · exact byPlane hpl.hs
  · exact byPlane hpl.mcl
  · exact byPlane hpl.he
  · exact byPlane hpl.ru
  · exact byPlane hpl.suz
  · exact byPlane hpl.on
  · exact byPlane hpl.co1
  · exact byPlane hpl.co2
  · exact byPlane hpl.co3
  · exact bySection hsec.fi22
  · exact bySection hsec.fi23
  · exact bySection hsec.fi24
  · exact byPlane hpl.hn
  · exact byPlane hpl.ly
  · exact byPlane hpl.th
  · exact bySection hsec.b
  · obtain ⟨H, K, hK, ⟨φ⟩⟩ := exists_section_of_quotient_subgroup N L
    have h4 := hsec.m X H K (L ⧸ Subgroup.center L) hnab ⟨φ⟩ ⟨e⟩
    omega

end CFSG.RankThree.PartOne

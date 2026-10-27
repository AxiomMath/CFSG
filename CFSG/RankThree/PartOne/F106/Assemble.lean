module

public import CFSG.RankThree.PartOne.K156.Full
public import CFSG.RankThree.PartOne.MB3.Defs

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def MovingQuasisimpleFive : Prop :=
  SchreierFor InCatalog → TwoActionInputs →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), SteinbergBM.SectionTenSetup G 5 A →
    ∀ K ∈ sectionTenZero 5 A, CFSG.IsQuasisimple K

theorem full106_of_seven_five (h7 : MB3.MovingQuasisimpleSeven) (h5 : MovingQuasisimpleFive) :
    K156.Full106Stmt := by
  intro hS hTwo G _ _ p A hsetup L hL
  have hcut := nonquasisimple_moving_theta_component_prime_cut hTwo G
    (sectionTenSetup_evenRank_eq hsetup).le p (sectionTenSetup_prime hsetup)
    (sectionTenSetup_three_lt hsetup) (sectionTenSetup_vanishing hsetup) A
    hsetup.2.2.2.2.2.2.1 hsetup.2.2.2.2.2.2.2.1 L hL
  rcases hcut with hq | rfl | rfl
  · exact hq
  · exact h5 hS hTwo G A hsetup L hL
  · exact h7 hS hTwo G A hsetup L hL

end CFSG.RankThree.PartOne.F106

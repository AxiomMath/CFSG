module

public import CFSG.RankThree.PartOne.K156.Full
public import CFSG.RankThree.PartOne.K156.FiveQuad
public import CFSG.RankThree.PartOne.K156.Row9
public import CFSG.RankThree.PartOne.U5K.Pkg.Mod

public section

namespace CFSG.RankThree.PartOne.K156

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem h106Max_of_full (h106 : Full106Stmt) : SectionTenMaximalMovingThetaComponentsQuasisimple :=
  fun hS hT G _ _ p A hsetup L hL => h106 hS hT G p A hsetup L
    ((sectionTenZeroStar_subset p A).1 hL)

theorem le_lieGenerated_of_zeroStar_five
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h128 : Node128) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {B : Subgroup G}
    (hB : B ∈ admissibleTriples p E) {Y : Subgroup G} (hY : Y ∈ sectionTenZeroStar p B) :
    Y ≤ lieGenerated p E := by
  obtain ⟨c', -, -, -, h', hF', h15', hout', hYE⟩ := exists_quad_five hS hTwo h106 h11 h122 h122b
    h123 h124 h125 h128 U5K.kfU5Mod_holds h15 hF hout hB hY
  obtain ⟨hcard, hrow, -⟩ := U5K.Pkg.rows h15' hF' hout'
  obtain ⟨f, -, -, -, -, hE4, -⟩ := hout
  exact row9_le (psuFourEvenCenterTrivial_of_multipliers hGA) h' hF' hE4 hrow hcard hYE

theorem kf156_of_five
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hTwo : TwoActionInputs) (h106 : Full106Stmt) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h128 : Node128) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) :
    ∀ X ∈ thetaCompZeroE p E, X ≤ lieGenerated p E := by
  intro X hX
  obtain ⟨B, hB, hXz⟩ := hX
  have hsetup := h15.h12.setup_of_admissible hB
  obtain ⟨Y, hY, hXY⟩ := exists_zeroStar_above_of_zero hS hsetup hXz
  have hYI := le_lieGenerated_of_zeroStar_five hGA hS hTwo (h106Max_of_full h106) h11 h122 h122b
    h123 h124 h125 h128 h15 hF hout hB hY
  have hXq : CFSG.IsQuasisimple ↥X := h106 hS hTwo G p B hsetup X hXz
  exact (le_of_sectionTenRel_of_quasisimple h15.h12.prime hXq hXY).trans hYI

end CFSG.RankThree.PartOne.K156

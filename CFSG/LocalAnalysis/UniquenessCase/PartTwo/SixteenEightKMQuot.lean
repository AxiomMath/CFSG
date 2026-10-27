module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16k_mQuot_le_rk (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (U Z : Subgroup (Vtil V₀ V hV)) (t : MulAut (Vtil V₀ V hV)) :
    E3.mQuot (commSub U (Subgroup.zpowers t) ⊔ Z) Z ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  have hCD : commSub U (Subgroup.zpowers t) ≤ commSub ⊤ (Subgroup.zpowers t) :=
    commSub_mono le_top le_rfl
  have hcard : Nat.card ↥(commSub U (Subgroup.zpowers t)) ∣
      Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) := Subgroup.card_dvd_of_le hCD
  have hrel : Z.relIndex (commSub U (Subgroup.zpowers t)) ∣
      Nat.card ↥(commSub U (Subgroup.zpowers t)) :=
    Subgroup.relIndex_dvd_card Z (commSub U (Subgroup.zpowers t))
  have hrelD : Z.relIndex (commSub U (Subgroup.zpowers t)) ∣
      Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) := hrel.trans hcard
  have hsup : Z.relIndex (commSub U (Subgroup.zpowers t) ⊔ Z) =
      Z.relIndex (commSub U (Subgroup.zpowers t)) :=
    Subgroup.relIndex_sup_right (H := commSub U (Subgroup.zpowers t)) (K := Z)
  show padicValNat 2 (Z.relIndex (commSub U (Subgroup.zpowers t) ⊔ Z)) ≤
    rk ↥(commSub ⊤ (Subgroup.zpowers t))
  rw [hsup]
  exact padicValNat_two_le_of_dvd (card_subgroup_pos _).ne' hrelD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

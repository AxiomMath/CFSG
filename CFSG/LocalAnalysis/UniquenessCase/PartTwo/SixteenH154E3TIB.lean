module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23CoreA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_cross_centralize (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    L ≤ Subgroup.centralizer ((conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x :
      Subgroup G) : Set G) ∧
    conjSubgroup L x ≤ Subgroup.centralizer ((wSub ⊥ V h.hyp151.isElemAbelian L :
      Subgroup G) : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hxs : x ∈ stabTil ⊥ V := hMs hxM
  have hLst : L ≤ stabTil ⊥ V := h.hyp151.le.trans hMs
  have hLxM : conjSubgroup L x ≤ D.M := by
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hxM) (h.hyp151.le hy)) hxM
    rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at hy'
  have hLxst : conjSubgroup L x ≤ stabTil ⊥ V := hLxM.trans hMs
  constructor
  · intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwsub : w ∈ wSub ⊥ V hV (conjSubgroup L x) := by
      rw [s15_Infra_wSub_conjSubgroup ⊥ V L hV hxs]
      exact hw
    have hwV : w ∈ V := preTil_le ⊥ V hV _ hwsub
    have hmkW : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
        wTil ⊥ V hV (conjSubgroup L x) :=
      (mem_preTil_iff_of_mem ⊥ V hV _ hwV).1 hwsub
    have hfix : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ fixV (barSub ⊥ V hV L) := by
      rw [mem_fixV]
      intro a ha
      exact c23_fix_wTil_conj h.hyp151 hV hxM hxn a ha _ hmkW
    exact (mul_inv_eq_iff_eq_mul.mp
      ((s16c7_mem_fixV_barSub_iff V hV hLst (IntMod.mk hV ⟨w, hwV⟩)).1 hfix l hl)).symm
  · intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwV : w ∈ V := preTil_le ⊥ V hV _ hw
    have hmkW : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈ wTil ⊥ V hV L :=
      (mem_preTil_iff_of_mem ⊥ V hV _ hwV).1 hw
    have hfix : wTil ⊥ V hV L ≤ fixV (barSub ⊥ V hV (conjSubgroup L x)) :=
      commSub_eq_bot_iff.1 (h.hyp151.commute x hxM hxn).2
    exact (mul_inv_eq_iff_eq_mul.mp
      ((s16c7_mem_fixV_barSub_iff V hV hLxst (IntMod.mk hV ⟨w, hwV⟩)).1
        (hfix hmkW) k hk)).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

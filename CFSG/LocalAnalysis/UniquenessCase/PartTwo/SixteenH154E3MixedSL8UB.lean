module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoTrans
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_sl28_cover_cent_zx (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKbar : barSub ⊥ V h.hyp151.isElemAbelian K =
      barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    K ≤ centralizer ((conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓
      Subgroup.centralizer (L : Set G)) x : Subgroup G) : Set G) := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp16.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hKs : K ≤ stabTil ⊥ V := hK.1.le.trans hMs
  have hxN : x ∈ normalizer (V : Set G) := h125.pairFacts.le_normalizer hxM
  have hY : conjSubgroup L x ≤ stabTil ⊥ V := by
    have hMconj : conjSubgroup D.M x = D.M :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hxM)
    calc conjSubgroup L x ≤ conjSubgroup D.M x := E3.conjSubgroup_mono_left x h.hyp151.le
      _ = D.M := hMconj
      _ ≤ stabTil ⊥ V := hMs
  have hZx_cent : conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x ≤
      Subgroup.centralizer (conjSubgroup L x : Set G) := by
    rw [← E3.conjSubgroup_centralizer L x]
    exact E3.conjSubgroup_mono_left x inf_le_right
  have hZx_V : conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x ≤ V := by
    have hWle : wSub ⊥ V hV L ≤ V := preTil_le ⊥ V hV _
    calc conjSubgroup (wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)) x
        ≤ conjSubgroup V x := E3.conjSubgroup_mono_left x (inf_le_left.trans hWle)
      _ = V := conjSubgroup_eq_iff_mem_normalizer.mpr hxN
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hwV : w ∈ V := hZx_V hw
  have hwc : ∀ y ∈ conjSubgroup L x, y * w * y⁻¹ = w := by
    intro y hy
    have hc := hZx_cent hw
    rw [Subgroup.mem_centralizer_iff] at hc
    have hyw : y * w = w * y := hc y hy
    rw [hyw]
    group
  have hfix : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
      fixV (barSub ⊥ V hV (conjSubgroup L x)) := by
    rw [s16c7_mem_fixV_barSub_iff V hV hY]
    intro y hy
    exact hwc y hy
  have hfixK : mkTil ⊥ V hV (IntMod.mk hV ⟨w, hwV⟩) ∈
      fixV (barSub ⊥ V hV K) := by
    rwa [← hKbar] at hfix
  have hcomm : k * w * k⁻¹ = w :=
    (s16c7_mem_fixV_barSub_iff V hV hKs (IntMod.mk hV ⟨w, hwV⟩)).1 hfixK k hk
  exact (mul_inv_eq_iff_eq_mul.mp hcomm).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

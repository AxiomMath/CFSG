module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8UAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
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

theorem s16h_e3_conj_cent_cases (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    ∀ m : D.M,
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
          (m : G) =
        wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G) ∨
      conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
          (m : G) =
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G)) x := by
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp16.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil ⊥ V := h.hyp151.le.trans hMs
  have hxstab : x ∈ stabTil ⊥ V := hMs hxM
  set W : Subgroup G := wSub ⊥ V hV L with hW
  set Z : Subgroup G := W ⊓ Subgroup.centralizer (L : Set G) with hZ
  have hWmem : W ∈ wConj D.M (⊥ : Subgroup G) V hV L := by
    refine ⟨1, D.M.one_mem, ?_⟩
    rw [conjSubgroup_one]
  have hWxmem : conjSubgroup W x ∈ wConj D.M (⊥ : Subgroup G) V hV L := by
    refine ⟨x, hxM, ?_⟩
    rw [hW]
  have hcard : (wConj D.M (⊥ : Subgroup G) V hV L).ncard = 2 := by
    rw [ncard_wConj D h.hyp151 hV]
    exact hs2
  have hWxne : W ≠ conjSubgroup W x := by
    intro heq
    have hmem : x ∈ D.M ⊓ normalizer (W : Set G) :=
      ⟨hxM, conjSubgroup_eq_iff_mem_normalizer.1 heq.symm⟩
    rw [hW, inf_normalizer_wSub_eq_nBar D h.hyp151 hV] at hmem
    exact hxn hmem
  have hpair : ({W, conjSubgroup W x} : Set (Subgroup G)) =
      wConj D.M (⊥ : Subgroup G) V hV L := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · rintro Y (rfl | rfl)
      · exact hWmem
      · exact hWxmem
    · rw [hcard, Set.ncard_pair hWxne]
  have hconjL_le : ∀ {g : G}, g ∈ D.M → conjSubgroup L g ≤ stabTil ⊥ V := by
    intro g hg
    have hc : conjSubgroup D.M g = D.M :=
      conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg)
    exact (E3.conjSubgroup_mono_left g h.hyp151.le).trans ((le_of_eq hc).trans hMs)
  intro m
  have hmstab : (m : G) ∈ stabTil ⊥ V := hMs m.2
  have hconjWm : conjSubgroup W (m : G) =
      wSub ⊥ V hV (conjSubgroup L (m : G)) :=
    (s15_Infra_wSub_conjSubgroup ⊥ V L hV hmstab).symm
  have hconjWx : conjSubgroup W x = wSub ⊥ V hV (conjSubgroup L x) :=
    (s15_Infra_wSub_conjSubgroup ⊥ V L hV hxstab).symm
  by_cases hmW : conjSubgroup W (m : G) = W
  · left
    have hbar : barSub ⊥ V hV (conjSubgroup L (m : G)) = barSub ⊥ V hV L := by
      rcases c23_barSub_conj_cases D h.hyp151 hV hs2 hxM hxn (m := (m : G)) m.2 with hc | hc
      · exact hc
      · exfalso
        have hws : wSub ⊥ V hV (conjSubgroup L (m : G)) =
            wSub ⊥ V hV (conjSubgroup L x) := by
          unfold wSub wTil
          rw [hc]
        have heq : W = conjSubgroup W x :=
          hmW.symm.trans (hconjWm.trans (hws.trans hconjWx.symm))
        exact hWxne heq
    calc conjSubgroup Z (m : G)
        = conjSubgroup W (m : G) ⊓
            Subgroup.centralizer (conjSubgroup L (m : G) : Set G) := by
          rw [hZ, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
      _ = W ⊓ Subgroup.centralizer (conjSubgroup L (m : G) : Set G) := by rw [hmW]
      _ = W ⊓ Subgroup.centralizer (L : Set G) := by
          rw [hW]
          exact s16h_e3_inf_centralizer_eq_of_barSub_eq hV hLstab
            (hconjL_le m.2) hbar.symm
      _ = Z := by rw [hZ]
  · right
    have hbar : barSub ⊥ V hV (conjSubgroup L (m : G)) =
        barSub ⊥ V hV (conjSubgroup L x) := by
      rcases c23_barSub_conj_cases D h.hyp151 hV hs2 hxM hxn (m := (m : G)) m.2 with hc | hc
      · exfalso
        have hws : wSub ⊥ V hV (conjSubgroup L (m : G)) = W := by
          have h1 : wTil ⊥ V hV (conjSubgroup L (m : G)) = wTil ⊥ V hV L :=
            congrArg (fun X => commSub ⊤ X) hc
          have h2 : wSub ⊥ V hV (conjSubgroup L (m : G)) = wSub ⊥ V hV L :=
            congrArg (fun S => preTil ⊥ V hV S) h1
          rw [h2, hW]
        exact hmW (hconjWm.trans hws)
      · exact hc
    have hWm_eqWx : conjSubgroup W (m : G) = conjSubgroup W x := by
      have hmem : conjSubgroup W (m : G) ∈ ({W, conjSubgroup W x} : Set (Subgroup G)) := by
        rw [hpair]
        exact ⟨(m : G), m.2, rfl⟩
      rcases hmem with hmem | hmem
      · exact absurd hmem hmW
      · exact hmem
    calc conjSubgroup Z (m : G)
        = conjSubgroup W (m : G) ⊓
            Subgroup.centralizer (conjSubgroup L (m : G) : Set G) := by
          rw [hZ, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
      _ = conjSubgroup W x ⊓
            Subgroup.centralizer (conjSubgroup L (m : G) : Set G) := by rw [hWm_eqWx]
      _ = conjSubgroup W x ⊓
            Subgroup.centralizer (conjSubgroup L x : Set G) := by
          rw [hconjWx]
          exact s16h_e3_inf_centralizer_eq_of_barSub_eq hV (hconjL_le hxM)
            (hconjL_le m.2) hbar.symm
      _ = conjSubgroup (W ⊓ Subgroup.centralizer (L : Set G)) x := by
          rw [E3.conjSubgroup_inf, E3.conjSubgroup_centralizer]
      _ = conjSubgroup Z x := by rw [hZ]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

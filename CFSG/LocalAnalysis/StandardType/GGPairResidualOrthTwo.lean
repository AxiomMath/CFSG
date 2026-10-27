module

public import CFSG.LocalAnalysis.StandardType.GGNbrD4TwoUnitaryBase
public import CFSG.LocalAnalysis.StandardType.GGResidualRk1ExcTops
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameOfMarking
public import CFSG.LocalAnalysis.StandardType.GGOrthWeakFrameCenter
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseOrthFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem orthTwo_elim {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (htwo : GGInnerDiagOnLabel
      (fun p lab => lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) p Bs X) :
    GGInnerDiagOnLabel (fun p lab => ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) p Bs X ∨
      GGInnerDiagOnLabel (fun p lab => (lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) ∧
        ¬ (lab.tag = .D ∧ lab.rank = 4)) p Bs X := by
  have hsplit : GGInnerDiagOnLabel (fun p lab => (ggRowP_EOmP p lab ∧ lab.n = 1 ∧ lab.rank = 4) ∨
      ((lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) ∧
        ¬ (lab.tag = .D ∧ lab.rank = 4))) p Bs X := by
    refine htwo.mono_label fun lab hl => ?_
    by_cases h4 : lab.tag = .D ∧ lab.rank = 4
    · refine Or.inl ⟨?_, hl.1, h4.2⟩
      rcases hl.2 with hP | hM
      · exact hP
      · exact absurd (h4.1.symm.trans hM.1) (by decide)
    · exact Or.inr ⟨hl, h4⟩
  exact GGInnerDiagOnLabel.elim_or hsplit

private theorem center_eq_bot_of_orthTwo_ne_D4
    {G : Type} [Group G] [Finite G] {p : ℕ} {X : Subgroup G} [Group.IsPerfect X]
    (lab : LargeEvenLabel)
    (hl : (lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) ∧ ¬ (lab.tag = .D ∧ lab.rank = 4))
    (hhas : GGHasLabel lab (↥X ⧸ Subgroup.center ↥X)) : Subgroup.center ↥X = ⊥ := by
  obtain ⟨⟨hn, hrow⟩, h4⟩ := hl
  refine OrthTorus.center_eq_bot_of_hasLabel_orth_two ?_ hn hhas
  rcases hrow with hP | hM
  · have h4' : lab.rank ≠ 4 := fun h => h4 ⟨hP.1, h⟩
    exact Or.inl ⟨hP.1, by have := hP.2.1; omega⟩
  · exact Or.inr ⟨hM.1, by have := hM.2.1; omega⟩

section Pair


theorem ggPairConcl_of_orthogonal_two
    (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (𝒦 : Finset (Subgroup G))
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (X : Subgroup G) (hX : X = L ∨ X ∈ 𝒦)
    (htwo : GGInnerDiagOnLabel
      (fun p lab => lab.n = 1 ∧ (ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab)) p Bs X)
    (r : MulAut ↥Bs) (hrA : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e)
    (s : MulAut ↥Bs) (hsA : s ∈ ggAutomizer X Bs) (hsC : s ∈ ggCoxRefl M e)
    (hne : r ≠ s) : GGPairConcl Bs X r s := by
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  let : Fact p.Prime := ⟨hp⟩
  have hrefl := ggCoxRefl_isReflection hpres.2 hrC
  have hsrefl := ggCoxRefl_isReflection hpres.2 hsC
  rcases hX with rfl | hX
  · have hZ := GGConfig.center_eq_bot_of_orthTwo ggLabelRigidInput_holds hcfg.1.1
      (htwo.mono_label fun _ hl => ⟨hl.2, hl.1⟩)
    exact OrthTorus.pair_of_orthogonal_marking ggLabelRigidInput_holds hp2
      (ggRouteCfg_isElemAbelian hcfg) hcfg.1.1.2.1.2.2.2 (fun _ hl => hl.2) htwo
      (fun _ _ _ => hZ) r s hrA hsA hrefl hsrefl hne
  have hw := GGSecFiveWeakNbr.of_mem hcfg hX
  by_cases hA : GGIsWeylMatrixA M
  · exact (ggResidual_orthRow_absurd_A ggLabelRigidInput_holds hcfg hpres hle3 hA (Or.inr hw)
      (htwo.mono_label fun _ hl => hl.2)).elim
  obtain ⟨y, hnb⟩ := hw.1
  rcases orthTwo_elim htwo with h4 | hrest
  · have hZ := hcfg.center_eq_bot_of_D4two_nbr ggLabelRigidInput_holds hpres hle3 hns hA hnb h4
    exact OrthTorus.pair_of_orthogonal_marking ggLabelRigidInput_holds hp2
      (ggRouteCfg_isElemAbelian hcfg) hcfg.1.1.2.1.2.2.2 (fun _ hl => Or.inl hl.1) h4
      (fun _ _ _ => hZ) r s hrA hsA hrefl hsrefl hne
  · let : Group.IsPerfect X := ⟨hrest.1⟩
    exact OrthTorus.pair_of_orthogonal_marking ggLabelRigidInput_holds hp2
      (ggRouteCfg_isElemAbelian hcfg) hcfg.1.1.2.1.2.2.2 (fun _ hl => hl.1.2) hrest
      (fun lab hl hhas => center_eq_bot_of_orthTwo_ne_D4 lab hl hhas)
      r s hrA hsA hrefl hsrefl hne

end Pair

end CFSG.StandardType

end

module

public import CFSG.Walter.Bender1970.S2.Subnormal
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45SzFix
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.RankThree.LocalRank.InvolutionCentralizerLocalRank
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem components_step2_of_le_normalizer
    {X : Type*} [Group X] [Finite X] {K W : Subgroup X}
    (hK : CFSG.IsComponent K) (hW2 : IsPGroup 2 W)
    (hKW : K ≤ Subgroup.normalizer (W : Set X)) :
    ⁅K, W⁆ = ⊥ := by
  classical
  have hcommW : ⁅K, W⁆ ≤ W := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_left).mp hKW
  have hcommLayer : ⁅K, W⁆ ≤ CFSG.layer X := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_le]
    intro w hw k hk
    rw [commutatorElement_def]
    have hKcomp : CFSG.IsComponent
        (K.map (MulAut.conj w).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj w) hK
    have hmem : w * k * w⁻¹ ∈ K.map (MulAut.conj w).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom hk
    exact (CFSG.layer X).mul_mem
      (CFSG.LocalCores.component_le_layer hKcomp hmem)
      (CFSG.LocalCores.component_le_layer hK (K.inv_mem hk))
  have hKWU0 : ⁅K, W⁆ ≤ W ⊓ CFSG.layer X := le_inf hcommW hcommLayer
  let U0 : Subgroup X := W ⊓ CFSG.layer X
  have hKnormLayer : K ≤ Subgroup.normalizer (CFSG.layer X : Set X) := by
    intro k hk
    rw [CFSG.layer.eq_sSup]
    exact CFSG.Walter.mem_normalizer_sSup_of_map_mem
      (fun L hL => CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj k) hL)
      (fun L hL => CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj k⁻¹) hL)
  have hKnormU0 : K ≤ Subgroup.normalizer (U0 : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro k hk u hu
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hKW hk) u).mp hu.1,
      (Subgroup.mem_normalizer_iff.mp (hKnormLayer hk) u).mp hu.2⟩
  have hlayerK : ⁅CFSG.layer X, K⁆ ≤ K := by
    rw [CFSG.layer.eq_sSup]
    refine CFSG.Walter.commutator_sSup_le (𝒜 := {L : Subgroup X | CFSG.IsComponent L}) K K ?_ ?_
    · intro L hL
      rcases CFSG.LocalCores.distinct_components_commute hL hK with heq | hbot
      · rw [heq]
        rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [commutatorElement_def]
        exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)
      · rw [hbot]
        exact bot_le
    · intro L hL
      rcases CFSG.LocalCores.distinct_components_commute hL hK with heq | hbot
      · rw [heq]
        exact Subgroup.le_normalizer
      · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot).trans
          (Subgroup.centralizer_le_normalizer (K : Set X))
  have hU0K_K : ⁅U0, K⁆ ≤ K :=
    (Subgroup.commutator_mono inf_le_right le_rfl).trans hlayerK
  have hU0K_W : ⁅U0, K⁆ ≤ W :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).mp hKW)
  have hU0K_U0 : ⁅U0, K⁆ ≤ U0 :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hKnormU0
  have hnormal : ((⁅U0, K⁆).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU0K_K).mpr
      (Subgroup.normalizer_commutator_ge_right U0 K)
  have h2 : IsPGroup 2 ((⁅U0, K⁆).subgroupOf K) :=
    (hW2.to_le hU0K_W).of_equiv (Subgroup.subgroupOfEquivOfLe hU0K_K).symm
  have hU0K_bot : ⁅U0, K⁆ = ⊥ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hnormal with htop | hcenter
    · exfalso
      haveI : Group.IsPerfect K := hK.1.1
      haveI : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
      have htop2 : IsPGroup 2 (⊤ : Subgroup K) := htop ▸ h2
      haveI : Group.IsNilpotent ↥(⊤ : Subgroup K) := htop2.isNilpotent
      have hnil : Group.IsNilpotent K :=
        Group.nilpotent_of_mulEquiv (Subgroup.topEquiv (G := K))
      exact Group.IsPerfect.not_isNilpotent K hnil
    · have hcentX : ⁅U0, K⁆ ≤ Subgroup.centralizer (K : Set X) := by
        intro q hq
        have hqK : q ∈ K := hU0K_K hq
        have hqcenter : (⟨q, hqK⟩ : K) ∈ Subgroup.center K :=
          hcenter (Subgroup.mem_subgroupOf.mpr hq)
        rw [Subgroup.mem_center_iff] at hqcenter
        intro y hy
        exact congrArg Subtype.val (hqcenter ⟨y, hy⟩)
      have hdouble : ⁅⁅U0, K⁆, K⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentX
      have hdouble' : ⁅⁅K, U0⁆, K⁆ = ⊥ := by
        rw [Subgroup.commutator_comm K U0]
        exact hdouble
      have hfinal := CFSG.LocalCores.perfect_double_commutator (P := K) (X := U0)
        hK.1.1 hdouble'
      rw [Subgroup.commutator_comm]
      exact hfinal
  have hdouble : ⁅⁅K, W⁆, K⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    exact (Subgroup.commutator_mono hKWU0 le_rfl).trans (le_of_eq hU0K_bot)
  exact CFSG.LocalCores.perfect_double_commutator (P := K) (X := W) hK.1.1 hdouble

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

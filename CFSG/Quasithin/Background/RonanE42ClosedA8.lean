module

public import CFSG.Quasithin.Background.RonanE42Closed
public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.RankThree.SubgroupLists.SL2Perfect
public import CFSG.GroupTheory.NonabelianSimpleOrderSixty
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofL2KFact
public import CFSG.Milestones.ASVolI.E4
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingOuterBound
public import CFSG.Open.StatedAPI
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.RankThree.SubgroupLists.CentralizerPerfect
public import CFSG.RankThree.SubgroupLists.IrreducibleGL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3IrrRed
public import CFSG.LocalAnalysis.SeitzReduction.PerfectCentralizer
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven
public import CFSG.RankThree.SubgroupLists2.OmegaThree
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Quasithin.Background.A3FactsA134
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123SylowA7
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1Orbit
public import CFSG.Quasithin.H13.GoldschmidtC137S168Main
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3L3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Psu3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3SmArith
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Klein
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3Five
public import CFSG.Quasithin.EmptyFaithful.S146zYOutPSL
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order
public import TauCeti.GroupTheory.Perm.Jordan
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7
public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Walter.J1Props
public import CFSG.Walter.J1Recog
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.Statements

public section

namespace CFSG.Quasithin.RonanE42.Closed

open CFSG.ComponentClassification.OuterAutomorphisms CFSG.Open

theorem eq_top_of_index_le_four {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    {H : Subgroup G} (h : H.index ≤ 4) : H = ⊤ := by
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ H) = H.index := by
    rw [← Nat.card_eq_fintype_card]; rfl
  let f : G →* Equiv.Perm (G ⧸ H) := MulAction.toPermHom G (G ⧸ H)
  have hdvd : Nat.card f.range ∣ 48 := by
    have h1 : Nat.card f.range ∣ Nat.card (Equiv.Perm (G ⧸ H)) :=
      Subgroup.card_subgroup_dvd_card _
    have h2 : Nat.card (Equiv.Perm (G ⧸ H)) = H.index.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcard]
    rw [h2] at h1
    exact h1.trans ((Nat.factorial_dvd_factorial h).trans (by decide))
  have hsolv : Group.IsSolvable ↥f.range :=
    CFSG.Quasithin.A38c15.hess_isSolvable_of_card_dvd hdvd
  have hperf : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  have hsub : Subsingleton ↥f.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isSolvable ↥f.range hsolv
  rw [eq_top_iff]
  intro g _
  have h1 : f g = 1 := by
    have := Subsingleton.elim (⟨f g, g, rfl⟩ : ↥f.range) 1
    exact congrArg Subtype.val this
  have h2 : g • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
    have := congrArg (fun π : Equiv.Perm (G ⧸ H) => π (QuotientGroup.mk 1)) h1
    simpa [f] using this
  have h3 : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk 1 := by
    simpa using h2
  have h4 := QuotientGroup.eq.mp h3
  simpa using h4

end CFSG.Quasithin.RonanE42.Closed

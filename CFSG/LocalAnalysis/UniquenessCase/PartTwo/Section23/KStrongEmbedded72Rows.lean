module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Setup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72L2Three
public import CFSG.Adapters.LieModelSimple
public import CFSG.GH74.KGroups.PSL2
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem eq_of_le_of_normal_of_isSimpleGroup {X : Type} [Group X] {K L : Subgroup X}
    [hKn : K.Normal] (hKL : K ≤ L) (hKs : IsSimpleGroup ↥K)
    (hLs : IsSimpleGroup ↥L) : K = L := by
  have hKne : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  have hsubN : (K.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 (by
      rw [Subgroup.normalizer_eq_top]
      exact le_top)
  have hsubne : K.subgroupOf L ≠ ⊥ := by
    intro h
    apply hKne
    have hd : Disjoint K L := (Subgroup.subgroupOf_eq_bot).1 h
    rw [disjoint_iff, inf_of_le_left hKL] at hd
    exact hd
  have htop : K.subgroupOf L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf L) with h | h
    · exact absurd h hsubne
    · exact h
  exact le_antisymm hKL (Subgroup.subgroupOf_eq_top.1 htop)

theorem kf7_l2_case {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {X : Type} [Group X] [Finite X] (hO : CFSG.pPrimeCore p X = ⊥)
    {L N : Subgroup X} (hLN : L.Normal) (hKL : genFittingFStar X ≤ L)
    (hshape : LieModel ↥L .PSL 2 p n) (hN : IsStronglyPEmbedded p N) :
    Group.IsSolvable ↥N := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup X := genFittingFStar X with hKdef
  obtain ⟨hKs, -, hKn, hKC, -⟩ := kf7_setup hp hp2 hO hLN hKL hN
  haveI : K.Normal := hKn
  have hLsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hshape
  have hKLeqL : K = L := eq_of_le_of_normal_of_isSimpleGroup hKL hKs hLsimple
  have hmodel : CFSG.Open.StatedClassicalModel ↥L .PSL 2 p n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hshape (by decide)
  obtain ⟨eL⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_stated p n (by omega)
    (GaloisField.card p n (by omega)) hmodel
  have hKeq : K = CFSG.generalizedFitting X :=
    CFSG.Adapters.genFittingFStar_eq_foundations (G := X)
  refine isSolvable_of_mulEquiv_psl2GF_of_ne_two hp2 hn hO hN ?_
  rw [← hKeq]
  exact (MulEquiv.subgroupCongr hKLeqL).trans eL

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

module

public import CFSG.RankThree.PartTwo.Late.Glue
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Late

@[expose] def Item2012 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], PartTwoStanding G → partTwoS G = ∅ →
    ∀ A M N L : Subgroup G, A ∈ partTwoE G → M ∈ scriptM (gammaZero A : Set G) →
      N ∈ scriptM (A : Set G) → N ≠ M → L ∈ oTwoComponentsIn N →
      ¬ Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃*
        ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))

variable {G : Type} [Group G] [Finite G]

theorem gammaZero_eq_gamma_of_mem_partTwoE {A : Subgroup G} (hA : A ∈ partTwoE G) :
    gammaZero A = gamma 2 A :=
  aschCore_eq_gamma_of_isMulCommutative 2 hA.1.1 (pRank_eq_three_of_mem_partTwoE hA).ge

theorem item2012_of_not_hyp1921 (h2010 : Item2010)
    (h : ∀ (G : Type) [Group G] [Finite G] (A M N L : Subgroup G), ¬ Hyp1921 G A M N L) :
    Item2012 := by
  intro G _ _ hst hS A M N L hA hM hN hne hL hiso
  exact h G A M N L
    { toSec19Std := ⟨hst, hS, h2010 G hst hS⟩
      mem_partTwoE := hA
      mem_scriptM := by rw [← gammaZero_eq_gamma_of_mem_partTwoE hA]; exact hM
      mem_scriptM_N := hN
      ne := hne
      mem_oTwoComponentsIn := hL
      quotient_iso := hiso }

@[expose] def Item1922 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M N L : Subgroup G), Hyp1921 G A M N L →
    (∃ c : G, sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) ∧
      ¬ L ≤ M

end CFSG.RankThree.PartTwo

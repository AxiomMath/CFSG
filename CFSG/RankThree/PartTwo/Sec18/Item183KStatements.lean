module

public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec12.Item124Bar
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

structure Hyp183 (G : Type) [Group G] [Finite G] (A M : Subgroup G) (c : G) (K : Subgroup G) :
    Prop extends Sec18Std G A M where
  mem_A : c ∈ A
  ne_one : c ≠ 1
  mem_thetaComponentsAt : K ∈ thetaComponentsAt 3 c
  quotient_iso :
    Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
  inducesInnerMod : ∀ a ∈ A, InducesInnerMod a K (CFSG.Open.pCoreOf 2 K)

structure Diag183 (G : Type) [Group G] [Finite G] (A M : Subgroup G) (c : G) (K E : Subgroup G) :
    Prop extends Hyp183 G A M c K where
  mem_K : c ∈ K
  sectionCentralizer_eq :
    sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) = (Subgroup.zpowers c : Set G)
  inf_eq : A ⊓ K = Subgroup.zpowers c
  E_mem_partTwoE : E ∈ partTwoE G
  E_le : E ≤ (A ⊔ K) ⊓ Subgroup.normalizer (A : Set G)
  le_normalizer_E : A ≤ Subgroup.normalizer (E : Set G)
  inf_noncyclic : ¬ ∃ x : G, ((E ⊓ K : Subgroup G) : Set G) ⊆ (Subgroup.zpowers x : Set G)
  sectionCentralizer_noncyclic :
    ¬ ∃ x : G, sectionCentralizer E K (CFSG.Open.pCoreOf 2 K) ⊆ (Subgroup.zpowers x : Set G)
  sec12StdBar : Sec12.Sec12StdBar G E c K

@[expose] def Item183ET : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G) (c : G) (K E : Subgroup G),
    Diag183 G A M c K E → E ∈ partTwoT G

@[expose] def Item183NM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G) (c : G) (K E : Subgroup G),
    Diag183 G A M c K E → ∀ N ∈ scriptM (gamma 2 E : Set G), N = M

@[expose] def Item183K : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M : Subgroup G), Sec18Std G A M →
    ∀ c ∈ A, c ≠ 1 → ∀ K ∈ thetaComponentsAt 3 c,
      Nonempty (K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) →
      (∀ a ∈ A, InducesInnerMod a K (CFSG.Open.pCoreOf 2 K)) → K ≤ M

end CFSG.RankThree.PartTwo.Sec18

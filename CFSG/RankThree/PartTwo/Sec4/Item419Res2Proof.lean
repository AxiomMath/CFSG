module

public import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofTools
public import Certificates.Certificate3169
public import Certificates.Certificate8036
import CFSG.RankThree.PartTwo.Sec4.Item419Res2ProofCensus
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Perm.ChainSpec
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec13.Item138N
public import CFSG.RankThree.PartTwo.Sec4.Item4Res3Proof419
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Certificates.Certificate2267
public import Certificates.Certificate8033
import Certificates.Kernel.SporSch.Th.Orb2315
import Certificates.Kernel.SporSch.Th.Plane2320

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSU projSp)
open CFSG.Blueprint

@[expose] def Config419 (G : Type) [Group G] [Finite G] (L A : Subgroup G) (c a : G)
    (K : Subgroup G) : Prop :=
  SectionFourHyp G ∧ IsComponent L ∧
    Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A ∧ Nat.card A = 3 ^ 4 ∧
    A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c ∧ orderOf c = 3 ∧
    a ∈ A ∧ a ∉ Subgroup.zpowers c ∧ K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) ∧
    ∀ A₀ ∈ partTwoF G, Nat.card A₀ ≤ 3 ^ 4

@[expose] def K419E27 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A : Subgroup G) (c a : G) (K : Subgroup G),
    Config419 G L A c a K → IsType419 K →
      ∃ E : Subgroup G, E ≤ A ∧ Late.IsE27 E ∧
        ∃ T ∈ invariantPiSubgroups L E (piOf 2), ¬ T ≤ Subgroup.centralizer (E : Set G)

section Kinds


@[expose] def K419OneField : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A : Subgroup G) (c a : G) (K : Subgroup G),
    Config419 G L A c a K → IsType419 K →
    (∃ x ∈ A, InducesStdKind L x .field ∨ InducesStdKind L x .graphField) →
      InducesStdKind L a .field ∨ InducesStdKind L a .graphField

end Kinds

@[expose] def K419U4Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (n : ℕ), Odd n →
    Nonempty (L ≃* projSU 4 2 n) → ∀ a ∈ Subgroup.normalizer (L : Set G), orderOf a = 3 →
    a ∉ Subgroup.centralizer (L : Set G) → ∀ K : Subgroup G,
    K ≤ L ⊓ Subgroup.centralizer ({a} : Set G) →
    IsComponent (K.subgroupOf (L ⊓ Subgroup.centralizer ({a} : Set G))) → ¬ IsType419 K

open Res419Two

theorem isType419_or_unitary {K : Type} [Group K]
    (h : (∃ n : ℕ, ChevalleyExceptionalModel K .G2 2 n) ∨ Nonempty (K ≃* projSU 3 3 1) ∨
      (∃ n : ℕ, ReeTitsModel K .twistedF4 2 n) ∨ ReeTitsModel K .Tits 2 1 ∨
      (∃ n : ℕ, 2 ≤ n ∧ Nonempty (K ≃* projSp 2 (GaloisField 2 n))) ∨
      Nonempty (K ≃* alternatingGroup (Fin 6)) ∨
      (∃ m : ℕ, Odd m ∧ Nonempty (K ≃* projSU 3 2 m))) :
    IsType419 K ∨ ∃ m : ℕ, Odd m ∧ Nonempty (K ≃* projSU 3 2 m) := by
  rcases h with h | h | h | h | h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact Or.inr h

theorem item4_19NJ3_of_res2
    (h417 : Item4_17) (hU : Item4_19NUnitary) (hE : K419E27) (hOne : K419OneField)
    (hU4 : K419U4Odd) : Item4_19NJ3 := by
  intro G _ _ hG L hL A c hA h81 hAc hc a ha hac K hK hKc htype hF
  rcases isType419_or_unitary htype with ht | hU3
  swap
  · exact Or.inl (hU G hG L hL A c hA h81 hAc hc a ha hac K hK hKc hU3 hF)
  have hcfg : Config419 G L A c a K := ⟨hG, hL, hA, h81, hAc, hc, ha, hac, hK, hKc, hF⟩
  have hO2 : CFSG.pCore 2 G = ⊥ := pCore_two_eq_bot hG hA.prop h81
  obtain ⟨E, hEA, hE27, T, hT, hTE⟩ := hE G L A c a K hcfg ht
  have halt := h417 G hG hO2 L hL (fun A' E' c' m h => quad_le_four hF A' E' c' m h) A E c 4
    ⟨hA, h81, hAc, hc, hE27, hEA, T, hT, hTE⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_ne_comm_of_isComponent hKc
  have haL : a ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_of_le hL hK hx hy hxy
  have ha3 : a ^ 3 = 1 := hA.prop.2 a ha
  have ha1 : a ≠ 1 := fun h1 => hac (h1 ▸ Subgroup.one_mem _)
  have haC : a ∉ Subgroup.centralizer (L : Set G) := fun h => hac (hAc ▸ ⟨ha, h⟩)
  have hKL : K ≤ L := fun z hz => (hK hz).1
  rcases halt with h1 | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h9, -⟩ | ⟨h, -⟩ | ⟨-, hJ, -⟩ | ⟨h, -⟩ |
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨n, hn, hU4n⟩, -⟩ | ⟨-, h6, -⟩
  · exact Or.inl (hOne G L A c a K hcfg ht h1)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · obtain ⟨e⟩ := h9
    exact Or.inr (Or.inl ⟨a6_of_alt9 e haL ha3 haC hK ht, Or.inl ⟨e⟩⟩)
  · exact absurd h (by norm_num)
  · exact Or.inr (Or.inr ⟨a6_of_j3 hKL hJ ht, nonempty_quot_center_J3 hJ⟩)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · exact absurd h (by norm_num)
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact absurd ht (hU4 G L n hn hU4n a haL (orderOf_eq_prime ha3 ha1) haC K hK hKc)
  · obtain ⟨e⟩ := h6
    exact Or.inr (Or.inl ⟨a6_of_sp62 e haL ha3 haC hK ht, Or.inr ⟨e⟩⟩)

end CFSG.RankThree.PartTwo.Sec4

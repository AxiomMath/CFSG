module

public import CFSG.RankThree.PartTwo.KFacts.AutKindsStd

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Blueprint

section Defs


structure Frame611 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G)
    (d : G) : Prop where
  standing : PartTwoStanding G
  mem_S : A ∈ partTwoS G
  card_A : Nat.card A = 81
  c_mem : c ∈ A
  c_ne_one : c ≠ 1
  mem_L : L ∈ lZeroStarAt A c
  cent_L : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c
  iso_L : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * 2)))
  mem_E : E ∈ collectionIn (partTwoE G) A
  c_mem_E : c ∈ E
  mem_lZero : L ∈ lZero E
  mem_T : T ∈ fourGroupsMinus E
  T_le_L : T ≤ L
  T_theta : T ⊓ inSubgroup (aschbacherSolvableCore 3) L = ⊥
  d_mem : d ∈ E ⊓ Subgroup.centralizer (T : Set G)
  d_not_mem : d ∉ Subgroup.zpowers c
  d_field : KFacts.InducesStdKind L d .field
  inner_nine : Nat.card (autThetaQuot A L ⊓ (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
    MulAut (L ⧸ aschbacherSolvableCore 3 L)).range : Subgroup _) = 9

structure Cfg611 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G)
    (d : G) (S K : Subgroup G) : Prop extends Frame611 G A c L E T d where
  mem_Sub : S ∈ invariantPiSubgroups (Subgroup.centralizer {d} ⊓ Subgroup.centralizer (T : Set G))
    E (piOf 2)
  S_ne_bot : S ≠ ⊥
  S_comm : ⁅S, Subgroup.zpowers c⁆ = S
  mem_K : K ∈ lZeroStarAt A d
  cent_K : A ⊓ thetaQuotCentralizer K = Subgroup.zpowers d
  perf_le : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K
  c_not_cent : c ∉ thetaQuotCentralizer K
  S_norm : S ≤ Subgroup.normalizer (K : Set G)
  S_not_theta : ¬ ⁅S, K⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K

end Defs

end CFSG.RankThree.PartTwo.Sec8.Hering611

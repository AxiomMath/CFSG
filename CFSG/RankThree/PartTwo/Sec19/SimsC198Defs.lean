module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def IsType198 (Y : Type) [Group Y] : Prop :=
  Sec4.IsSLThreePi Y ∨ Sec4.IsTripleCover Y (alternatingGroup (Fin 7)) ∨
    Sec4.IsTripleCover Y CFSG.Blueprint.NativeSporadic.M22

@[expose] noncomputable def thetaIn {S : Type} [Group S] (L : Subgroup S) : Subgroup S :=
  (aschbacherSolvableCore 3 L).map L.subtype

structure RankHyp (X : Type) [Group X] [Finite X] : Prop where
  quasisimple : IsQuasisimple X
  pCore_two : CFSG.pCore 2 X = ⊥
  kGroup : CFSG.IsKGroup X
  rank_three : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3
  rank_prime : ∀ p : ℕ, p.Prime → 3 < p → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2

structure LocalDatum (S : Type) [Group S] [Finite S] (c : S) (L : Subgroup S) : Prop where
  orderOf_eq : orderOf c = 3
  le_centralizer : L ≤ Subgroup.centralizer ({c} : Set S)
  mem : c ∈ L
  subnormal : (L.subgroupOf (Subgroup.centralizer ({c} : Set S))).IsSubnormal
  perfect : Group.IsPerfect L
  quasisimple : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L)
  type : IsType198 (L ⧸ aschbacherSolvableCore 3 L)

structure AutDatum (S : Type) [Group S] [Finite S] (c : S) (L : Subgroup S)
    (𝒟 : Subgroup (MulAut S)) : Prop extends LocalDatum S c L where
  pow_three : ∀ φ ∈ 𝒟, φ ^ 3 = 1
  card : Nat.card 𝒟 = 9
  conj_mem : MulAut.conj c ∈ 𝒟
  map_eq : ∀ φ ∈ 𝒟, ∀ l : S, φ l ∈ L ↔ l ∈ L
  trivial : ∀ φ ∈ 𝒟, ∀ l ∈ L, φ l * l⁻¹ ∈ thetaIn L

@[expose] def NoLocalDatum (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (c : S) (L : Subgroup S), ¬ LocalDatum S c L

@[expose] def NoAutDatum (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (c : S) (L : Subgroup S) (𝒟 : Subgroup (MulAut S)), ¬ AutDatum S c L 𝒟

@[expose] def OuterAutDatum (S : Type) [Group S] [Finite S] : Prop :=
  ∀ (c : S) (L : Subgroup S) (𝒟 : Subgroup (MulAut S)), AutDatum S c L 𝒟 →
    ∃ φ ∈ 𝒟, φ ∉ (MulAut.conj : S →* MulAut S).range

end CFSG.RankThree.PartTwo.Sec19.SimsC198

module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartTwo.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree.PartTwo TauCeti

@[expose] def IsThreeCenterCover (G : Type) [Group G] [Finite G] (S : Type) [Group S] : Prop :=
  IsQuasisimple G ∧ 3 ∣ Nat.card (Subgroup.center G) ∧ Nonempty (G ⧸ Subgroup.center G ≃* S)

@[expose] def TripleCoverLieIndex : LieTypeIndex → Prop
  | .A r q => 3 ∣ r + 1 ∧ 3 ∣ q.card - 1
  | .twistedA r q => (3 ∣ r + 1 ∧ 3 ∣ q.card + 1) ∨ (r = 3 ∧ q.card = 3)
  | .B r q => r = 3 ∧ q.card = 3
  | .G2 q => q.card = 3
  | .E6 q => 3 ∣ q.card - 1
  | .twistedE6 q => 3 ∣ q.card + 1
  | _ => False

@[expose] def TripleCoverAlternating : Prop :=
  ∀ (n : ℕ) (G : Type) [Group G] [Finite G], 5 ≤ n →
    IsThreeCenterCover G (alternatingGroup (Fin n)) → n = 6 ∨ n = 7

@[expose] def TripleCoverSporadic : Prop :=
  ∀ (s : SporadicName) (G : Type) [Group G] [Finite G],
    IsThreeCenterCover G (CFSGIndex.sporadic s).Group →
      s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨ s = .Fi24Prime

@[expose] def TripleCoverLie : Prop :=
  ∀ (d : ValidLieTypeIndex) (G : Type) [Group G] [Finite G],
    IsThreeCenterCover G (CFSGIndex.lie d).Group → TripleCoverLieIndex d.1

structure TripleCoverInputs : Prop where
  alternating : TripleCoverAlternating
  sporadic : TripleCoverSporadic
  lie : TripleCoverLie

@[expose] def TripleCoverSuzRankFour : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsThreeCenterCover G (CFSGIndex.sporadic .Suz).Group →
    4 ≤ CFSG.twoLocalOddRank G

@[expose] def TripleCoverU62RankFour : Prop :=
  ∀ (q : PrimePower) (hv : (LieTypeIndex.twistedA 5 q).Valid), q.p = 2 → q.exponent = 1 →
    ∀ (G : Type) [Group G] [Finite G],
      IsThreeCenterCover G (CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group → 4 ≤ CFSG.twoLocalOddRank G

end CFSG.RankThree.PartTwo.Sec4.Census

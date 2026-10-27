module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step1917Proof

@[expose] def Alt1915W
    {G : Type} [Group G] [Finite G]
    (L K : Subgroup G) (c : G) : Prop :=
  K = L ⊔ CFSG.Open.pCoreOf 2 K ∨
    (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) p e ∧
      Sec4.IsoLThreePi (K ⧸ CFSG.pCore 2 K) p (3 * e) ∧ KFacts.InducesStdKind K c .field) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (L ⧸ CFSG.pCore 2 L) 2 n ∧
      CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K) .trialityD4 2 n ∧
      KFacts.InducesStdKind K c .graphField)

end Step1917Proof

@[expose] def Step1917J :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → L ≤ M → ∀ d ∈ A ⊓ E, d ∉ Subgroup.zpowers c →
      ¬ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ M →
      ∀ H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G), H ≠ M →
      ∀ K ∈ oTwoComponentsIn M, L ≤ K → Step1917Proof.Alt1915W L K c → K ∈ scriptJ M H →
        (IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K)) →
        ((IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            IsProperParabolic (starIm K H)) ∨
          (Nonempty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
            Sec4.IsExtOf (starIm K H) (Equiv.Perm (Fin 5)) (Multiplicative (Fin 4 → ZMod 2)))) →
        False

@[expose] def Step1917Push :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G)
    (hctx : Ctx1912 G A c L E M), L ≤ M → ∀ d ∈ A ⊓ E, d ∉ Subgroup.zpowers c →
      ¬ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ M →
      ∀ H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G), H ≠ M →
      ∀ K ∈ oTwoComponentsIn M, L ≤ K → Step1917Proof.Alt1915W L K c → K ≤ H →
        H ≤ Subgroup.normalizer (K : Set G) ∨
          (letI := Sec15.kerAO2_normal hctx.mem_lA.2.1;
            Nonempty (↥(A ⊔ L) ⧸ Sec15.kerAO2 A L ≃*
              Multiplicative (ZMod 3) × CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2)))

@[expose] def Step1917Lift :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G)
    (hctx : Ctx1912 G A c L E M), L ≤ M → ∀ d ∈ A ⊓ E, d ∉ Subgroup.zpowers c →
      ¬ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤ M →
      ∀ H ∈ scriptM (Subgroup.normalizer (Subgroup.zpowers d : Set G) : Set G), H ≠ M →
      ∀ K ∈ oTwoComponentsIn M, L ≤ K → Step1917Proof.Alt1915W L K c → K ≤ H →
        ¬ H ≤ Subgroup.normalizer (K : Set G) →
        (letI := Sec15.kerAO2_normal hctx.mem_lA.2.1;
          Nonempty (↥(A ⊔ L) ⧸ Sec15.kerAO2 A L ≃*
            Multiplicative (ZMod 3) × CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 2))) →
        K ∈ oTwoComponentsIn H

end CFSG.RankThree.PartTwo.Sec19

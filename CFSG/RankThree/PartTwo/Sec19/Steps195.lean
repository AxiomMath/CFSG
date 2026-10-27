module

public import CFSG.RankThree.PartTwo.Sec19.Statements
public import CFSG.RankThree.PartTwo.Sec13.Steps

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

structure Ctx195 (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G) :
    Prop extends Sec19Std G where
  mem_partTwoE : A ∈ partTwoE G
  not_mem_partTwoT : A ∉ partTwoT G
  zpowers_mem_omegaA : Subgroup.zpowers c ∈ omegaA A
  mem_lA : L ∈ lA A c
  mem_L : c ∈ L
  le_sup : E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G)
  isE27 : IsE27 E
  centralizer_noncyclic : ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G)
  inf_noncyclic : ¬ IsCyclic (E ⊓ L : Subgroup G)
  le_normalizer : A ≤ Subgroup.normalizer (E : Set G)
  mem_partTwoT : E ∈ partTwoT G
  mem_scriptM : M ∈ scriptM (gamma 2 E : Set G)

@[expose] def Step196 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ M

@[expose] def Step197 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → Sec4.IsSLThreePiTwo (lBarA c L A)

@[expose] def Alt198 {G : Type} [Group G] [Finite G] (L E K : Subgroup G) : Prop :=
  K = L ⊔ CFSG.Open.pCoreOf 2 K ∨
    ((∃ p f : ℕ, CFSG.Blueprint.ChevalleyExceptionalModel (K ⧸ CFSG.pCore 2 K) .trialityD4 p f) ∧
      ∃ e ∈ E ⊓ Sec4.thetaQuotCentralizer L, KFacts.InducesStdKind K e .graphField)

@[expose] def Step198 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → ∃ K ∈ oTwoComponentsIn M, L ≤ K ∧ Alt198 L E K

@[expose] def Step198D : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → Nat.card (E ⊓ A : Subgroup G) = 9

@[expose] def Step199 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → ¬ gammaOne (E ⊓ A) ≤ M

@[expose] def Step1910O2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → ∀ d ∈ E ⊓ A, d ∉ Subgroup.zpowers c →
      ¬ Subgroup.centralizer ({d} : Set G) ≤ M →
      2 < Nat.card (CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G)

@[expose] def Step1910 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → ∀ K ∈ oTwoComponentsIn M, L ≤ K → Alt198 L E K →
      ∀ d ∈ E ⊓ A, d ∉ Subgroup.zpowers c → ¬ Subgroup.centralizer ({d} : Set G) ≤ M →
        ∀ H ∈ scriptM (Subgroup.centralizer ({d} : Set G) : Set G), H ≠ M → K ∈ scriptJ M H

@[expose] def Step1911 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → ∀ K ∈ oTwoComponentsIn M, L ≤ K → Alt198 L E K →
      ∀ d ∈ E ⊓ A, d ∉ Subgroup.zpowers c →
        ∀ H ∈ scriptM (Subgroup.centralizer ({d} : Set G) : Set G), H ≠ M → K ∈ scriptJ M H →
          K = L ⊔ CFSG.Open.pCoreOf 2 K ∧ IsProperParabolic (starIm K H)

@[expose] def Step1911End : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx195 G A c L E M → ∀ K ∈ oTwoComponentsIn M, L ≤ K → K = L ⊔ CFSG.Open.pCoreOf 2 K →
      ∀ d ∈ E ⊓ A, d ∉ Subgroup.zpowers c →
        ∀ H ∈ scriptM (Subgroup.centralizer ({d} : Set G) : Set G), H ≠ M → K ∈ scriptJ M H →
          IsProperParabolic (starIm K H) → False

end CFSG.RankThree.PartTwo.Sec19

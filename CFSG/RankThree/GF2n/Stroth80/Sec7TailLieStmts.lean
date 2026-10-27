module

public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.CharacterTheory.Semidihedral.Principal.FreeSixCharacterDefectFourSupport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def OutSolvableListStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X], ListGroup X →
    ∀ P : Subgroup (MulAut X), commutator ↥P = ⊤ →
      P ≤ (MulAut.conj : X →* MulAut X).range

@[expose] def TwoRankSporadicAltStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ k : ℕ, 6 ≤ k ∧ k ≤ 9 ∧ Nonempty (X ≃* alternatingGroup (Fin k))) ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic X .M22 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic X .M23 ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic X .M24) →
    ∀ A : Subgroup X, IsElemAbelian 2 A → Nat.card A ≤ 2 ^ 6

@[expose] def BorelRankOneSolvableStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel X .PSL 2 2 s) ∨
      (∃ s : ℕ, 2 ≤ s ∧ StatedClassicalModel X .PSU 3 2 s) ∨
      (∃ s : ℕ, Odd s ∧ 3 ≤ s ∧ CFSG.Blueprint.LieModel X .twistedB2 0 2 s)) →
    ∀ T : Subgroup X, T ≠ ⊥ → IsPGroup 2 T →
      Group.IsSolvable ↥(Subgroup.normalizer (T : Set X))

@[expose] def ArtinLinearOrdersStatement : Prop :=
  ∀ (a b : ℕ) (K K' : Type) [Field K] [Finite K] [Field K'] [Finite K'], 2 ≤ a → 2 ≤ b →
    (∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f) → (∃ f : ℕ, 1 ≤ f ∧ Nat.card K' = 2 ^ f) →
    ¬ (a = 2 ∧ Nat.card K = 2) → ¬ (b = 2 ∧ Nat.card K' = 2) →
    Nat.card (StatedProj (StatedSL a K)) = Nat.card (StatedProj (StatedSL b K')) →
      (a = b ∧ Nat.card K = Nat.card K') ∨
      (a = 3 ∧ Nat.card K = 4 ∧ b = 4 ∧ Nat.card K' = 2) ∨
      (a = 4 ∧ Nat.card K = 2 ∧ b = 3 ∧ Nat.card K' = 4)

@[expose] def RadicalTwoSubgroupLinearStatement : Prop :=
  ∀ (r : ℕ) (K : Type) [Field K] [Finite K], 3 ≤ r → (∃ f : ℕ, 1 ≤ f ∧ Nat.card K = 2 ^ f) →
    ∀ U : Subgroup (StatedProj (StatedSL r K)), U ≠ ⊥ → IsPGroup 2 U →
      inSubgroup (pCore 2) (Subgroup.normalizer (U : Set (StatedProj (StatedSL r K)))) = U →
      ∃ (k : ℕ) (m : Fin k → ℕ) (hk : 2 ≤ k), (∀ i, 1 ≤ m i) ∧ ∑ i, m i = r ∧
        Nat.card ↥(Subgroup.center ↥U) =
          Nat.card K ^ (m ⟨0, by omega⟩ * m ⟨k - 1, by omega⟩) ∧
        Nat.card U = Nat.card K ^ ((r ^ 2 - ∑ i, m i ^ 2) / 2) ∧
        ∀ S : Subgroup (↥(Subgroup.normalizer (U : Set (StatedProj (StatedSL r K)))) ⧸
            U.subgroupOf (Subgroup.normalizer (U : Set (StatedProj (StatedSL r K))))),
          S.Normal → IsQuasisimple S →
            ∃ i, 2 ≤ m i ∧ ¬ (m i = 2 ∧ Nat.card K = 2) ∧
              ∃ Z' : Subgroup S, Z' ≤ Subgroup.center S ∧ ∃ _ : Z'.Normal,
                Nonempty ((S ⧸ Z') ≃* StatedProj (StatedSL (m i) K))

@[expose] def IsCoveringOf (P : ∀ (X : Type) [Group X], Prop) (H : Type) [Group H] : Prop :=
  commutator H = ⊤ ∧ ∃ Z : Subgroup H, Z ≤ Subgroup.center H ∧ ∃ _ : Z.Normal, P (H ⧸ Z)

@[expose] def Tim77Cor2AlphaList (X : Type) [Group X] : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ StatedClassicalModel X .PSL 3 2 m) ∨
  (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .G2 0 2 m) ∨
  StatedClassicalModel X .PSU 3 3 1 ∨
  (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .trialityD4 0 2 m) ∨
  Nonempty (X ≃* alternatingGroup (Fin 6)) ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic X .J2

@[expose] def Tim77Cor2BetaList (X : Type) [Group X] : Prop :=
  (∃ m : ℕ, 1 ≤ m ∧ StatedClassicalModel X .PSL 2 2 m) ∨
  (∃ m : ℕ, 1 ≤ m ∧ StatedClassicalModel X .PSU 3 2 m) ∨
  (∃ m : ℕ, 1 ≤ m ∧ CFSG.Blueprint.LieModel X .twistedB2 0 2 m)

@[expose] def HasNormalTwoComplement (X : Type) [Group X] : Prop :=
  ∃ O : Subgroup X, O.Normal ∧ Odd (Nat.card O) ∧ ∃ _ : O.Normal, IsPGroup 2 (X ⧸ O)

@[expose] def WAC {G : Type} [Group G] (A : Subgroup G) : Subgroup G :=
  ⨆ (g : G) (_ : conjSubgroup g A ≤ Subgroup.centralizer (A : Set G)), conjSubgroup g A

@[expose] def Tim77Cor2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian 2 A → IsTI A →
    ⁅WAC A, WAC A⁆ ≤ A → (∃ S : Sylow 2 G, (S : Subgroup G) ≤ Subgroup.normalizer (A : Set G)) →
    (WAC A = A ∧ ThmAConclusion A) ∨
    IsCoveringOf Tim77Cor2AlphaList ↥(Subgroup.normalClosure (A : Set G)) ∨
    (⁅WAC A, WAC A⁆ = ⊥ ∧
      ∃ (r : ℕ) (X : Fin r → Subgroup ↥(Subgroup.normalClosure (A : Set G))),
        (∀ i, (X i).Normal) ∧ (∀ i j, i ≠ j → ∀ x ∈ X i, ∀ y ∈ X j, x * y = y * x) ∧
        ⨆ i, X i = ⊤ ∧
        ∀ i, IsCoveringOf Tim77Cor2BetaList ↥(X i) ∨ HasNormalTwoComplement ↥(X i)) ∨
    (∃ (N : Subgroup ↥(Subgroup.normalClosure (A : Set G))) (_ : N.Normal), IsElemAbelian 2 N ∧
      Nat.card A = 2 * Nat.card ↥(A ⊓ N.map (Subgroup.normalClosure (A : Set G)).subtype) ∧
      ∃ Z : Subgroup (↥(Subgroup.normalClosure (A : Set G)) ⧸ N),
        Z ≤ Subgroup.center (↥(Subgroup.normalClosure (A : Set G)) ⧸ N) ∧
        ∃ _ : Z.Normal, Tim77Cor2BetaList ((↥(Subgroup.normalClosure (A : Set G)) ⧸ N) ⧸ Z))

end CFSG.RankThree.GF2n.Stroth80

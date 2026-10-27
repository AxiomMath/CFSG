module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTables
public import Certificates.Data.A8Nbr476

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

section Config

variable {G : Type} [Group G] [Finite G]

@[expose] def GGSecFiveA11Config (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) :
    Prop :=
  p = 7 ∧ StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 ∧
    ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 ∧
      ¬ GGReflGenerated p (ggAutomizer K Bs)

end Config

@[expose] def GGTablePAt (p : ℕ) (J X : Type) [Group J] [Group X] : Prop :=
  ∃ labJ labX : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ LargeEvenInLambda2 labX ∧
    GGTablePRow p labJ labX ∧ GGHasLabel labJ J ∧ GGHasLabel labX X

@[expose] def GGTwE6BadLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n + 1

@[expose] def GGNbrReflGenNonSplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) →
      LargeEvenMarking ↥K
        (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ GGTwE6BadLabel p lab) →
      GGReflGenerated p (ggAutomizer K Bs)

@[expose] def GGTwE6ThreeNbrRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → p = 3 → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      GGInnerDiagOnLab GGTwE6BadLabel p Bs K → ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
        GGTorusSelfCent 3 (ggGamma K hN).range → 3 ^ 5 ≤ Nat.card (ggGamma K hN).range

@[expose] def GGTwE6ThreeNbrWeylInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGTwE6BadLabel 3 lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusReflGenW 3 5 R I

@[expose] def GGNbrReflGenNonSplitFull : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) →
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1) →
      GGReflGenerated p (ggAutomizer K Bs)

@[expose] def GGSecFiveA8TablePInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        (GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
          GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) →
        (∀ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ →
          GGHasLabel labJ (J ⧸ Subgroup.center J) →
          GGTablePAt 7 (J ⧸ Subgroup.center J) (K ⧸ Subgroup.center K)) ∧
        (∀ labJ labL : LargeEvenLabel, LargeEvenInLambda2 labJ → LargeEvenInLambda2 labL →
          GGHasLabel labJ (J ⧸ Subgroup.center J) → GGHasLabel labL (L ⧸ Subgroup.center L) →
          GGTablePAt 7 (J ⧸ Subgroup.center J) (L ⧸ Subgroup.center L))

@[expose] def GGA8NbrCoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → p = 7 →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        StatedClassicalModel (K ⧸ Subgroup.center K) .PSL 9 2 1 →
        (GGHasLabel ⟨.A, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.C, 3, 3⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.twD, 4, 3⟩ (L ⧸ Subgroup.center L)) →
        ∃ (c : Certificates.A8Nbr476.Case) (ι : Additive ↥Bs ≃+ (Fin 4 → ZMod 7)),
          c ∈ Certificates.A8Nbr476.allCases ∧
          (∀ k : Fin 6, ∃ φ ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs, ∀ b : ↥Bs,
            ι (Additive.ofMul (φ b)) =
              Matrix.vecMul (ι (Additive.ofMul b)) (Certificates.A8Nbr476.gens c k)) ∧
          (c.1 = true → StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3)

section Input

@[expose] def GGSecFiveA11Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveA11Config p B Bs x L D J →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveN1Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ¬ GGScalarsPmOne Bs →
      GGSecFiveWeylCase' p B Bs x D J → GGSecFiveData p B x L D J

@[expose] def GGSecFiveN2Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J →
      (∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧ ¬ GGReflGenerated p (ggAutomizer K Bs)) →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveTwE6ResidualInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ¬ GGSecFiveWeylCase' p B Bs x D J →
      (∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
        ¬ LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) ∧
        LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGTwE6BadLabel p lab) ∧
        ¬ GGReflGenerated p (ggAutomizer K Bs)) →
      GGSecFiveData p B x L D J

@[expose] def GGSecFiveNonWeylKnown : Prop :=
  GGNbrReflGenNonSplitInput ∧ GGTwE6ThreeNbrRankInput ∧
    GGTwE6ThreeNbrWeylInput ∧ GGLabelCenterPCyclicInput ∧ GGTCJKnown ∧ GGSecFiveA8TablePInput ∧
    GGA8NbrCoordInput ∧ GGSecFiveA11Input

theorem ggSecFiveNonWeylInput_iff : GGSecFiveNonWeylInput ↔ GGSecFiveN2Input := by
  constructor
  · intro h G _ _ p B Bs x L D J hR ⟨y, K, hK, hn⟩
    exact h G p B Bs x L D J hR fun hW => hn (hW y K hK)
  · intro h2 G _ _ p B Bs x L D J hR hW
    unfold GGSecFiveWeylCase' at hW
    push Not at hW
    obtain ⟨y, K, hK, hn⟩ := hW
    exact h2 G p B Bs x L D J hR ⟨y, K, hK, hn⟩

theorem ggSecFiveA11Input_of_nonWeyl (h : GGSecFiveNonWeylInput) : GGSecFiveA11Input := by
  intro G _ _ p B Bs x L D J hR hA
  obtain ⟨-, -, y, K, hK, -, hn⟩ := hA
  exact ggSecFiveNonWeylInput_iff.1 h G p B Bs x L D J hR ⟨y, K, hK, hn⟩

theorem ggSecFiveTwE6ResidualInput_of_nonWeyl (h : GGSecFiveNonWeylInput) :
    GGSecFiveTwE6ResidualInput :=
  fun G _ _ p B Bs x L D J hR hW _ => h G p B Bs x L D J hR hW

end Input

end CFSG.StandardType

end

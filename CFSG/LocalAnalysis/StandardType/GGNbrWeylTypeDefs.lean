module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowNSDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def GGTorusWeylTypeW (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
    GGTorusTBGroup p r R I L' ψ A →
      ∃ (ι : Type) (M : CoxeterMatrix ι)
        (f : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)),
        GGIsWeylMatrix M ∧
          Nat.card ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) ≠ 12 ∧
          ∀ i : ι,
            ((f (M.simple i) :
              ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) : MulAut ↥A) ∈
              ggTorusReflSet p A

@[expose] def GGNbrTableBWeylTypeNonSplitOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    GGNbrNonSplitLabel p lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I)

@[expose] def GGNbrTableBWeylTypeSplitOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S p lab →
    LargeEvenHalfSplit p lab True → GGNbrSplitLabel p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusWeylTypeW p r R I

@[expose] def GGNbrTableBWeylTypeSplitInput : Prop :=
  GGNbrTableBWeylTypeSplitOn fun _ _ => True

@[expose] def GGNbrWeylTypeNonSplitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) →
      LargeEvenMarking ↥K
        (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ GGTwE6BadLabel p lab) →
      GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
        ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs)

@[expose] def GGF4ThreeNbrWeylTypeInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGF4ThreeLabel 3 lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW 3 4 R I

@[expose] def GGUSixThreeNbrWeylTypeInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGUSixThreeLabel 3 lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW 3 4 R I

@[expose] def GGTwE6ThreeNbrWeylTypeInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGTwE6BadLabel 3 lab →
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW 3 5 R I

@[expose] def GGNbrWeylTypeNonSplitFull : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) →
      LargeEvenMarking ↥K (fun lab _ _ _ _ _ => p ∣ (2 ^ lab.n) ^ 2 - 1) →
      GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
        ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs)

@[expose] def GGNbrExcSevenReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      p = 7 → (GGHasLabel ⟨.A, 8, 1⟩ (K ⧸ Subgroup.center K) ∨
        GGHasLabel ⟨.E6, 0, 1⟩ (K ⧸ Subgroup.center K)) →
      ¬ GGReflGenerated p (ggAutomizer K Bs)

@[expose] def GGSecFivePumpNbrNSSplitInput
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → ¬ GGSplitLie p K →
        LargeEvenMarking ↥K (fun lab _ _ _ _ _ => GGNbrSplitLabel p lab) →
        GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
          ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs)

end CFSG.StandardType

end

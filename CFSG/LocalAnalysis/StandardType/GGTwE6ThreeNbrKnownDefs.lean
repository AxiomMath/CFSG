module

public import CFSG.LocalAnalysis.StandardType.GGNbrOutsideInndiag
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGUnitaryCommLifts {L' : Type} [Group L'] (J₁ : Subgroup L') (n d : ℕ)
    (S : Set (MulAut L')) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
    ∀ θ : ↥J₁ ⧸ Subgroup.center ↥J₁ ≃* LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)),
      ∀ a₁ ∈ S, ∀ a₂ ∈ S, (∀ l ∈ J₁, a₁ l ∈ J₁) → (∀ l ∈ J₁, a₂ l ∈ J₁) →
        ∀ A₁ ∈ LargeEvenGUSet (Fin d) K (2 ^ n), ∀ A₂ ∈ LargeEvenGUSet (Fin d) K (2 ^ n),
          (∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk _) {A₁},
            LargeEvenInduces θ (fun l l' : ↥J₁ => (l' : L') = a₁ l) φ) →
          (∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk _) {A₂},
            LargeEvenInduces θ (fun l l' : ↥J₁ => (l' : L') = a₂ l) φ) →
          A₁ * A₂ = A₂ * A₁

@[expose] def GGTwE6SCFourSetting {R : Type} [Group R] (I : Set (MulAut R)) {L' : Type}
    [Group L'] (ψ : L' →* R) (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L') :
    Prop :=
  IsElemAbelian 3 A ∧ (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) ∧
    Nat.card A = 3 ^ 4 ∧ GGTorusSelfCent 3 A ∧ a₀ ∈ A ∧ a₀ ≠ 1 ∧
    IsComponentOf J₁ (ggFix a₀) ∧ (∀ a ∈ A, ∀ l ∈ J₁, a l ∈ J₁) ∧
    (∀ a ∈ A, (∀ l ∈ J₁, a l = l) → a ∈ Subgroup.zpowers a₀)

@[expose] def GGTwE6SCFourLabelsKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L'),
          GGTwE6SCFourSetting I ψ A a₀ J₁ →
          LargeEvenMarking ↥J₁ fun lab' _ _ _ _ _ =>
            (lab' = ⟨.D, 4, lab.n⟩ ∨ lab' = ⟨.triD4, 0, lab.n⟩ ∨ lab' = ⟨.A, 2, 3 * lab.n⟩ ∨
              lab' = ⟨.twA, 2, 3 * lab.n⟩) ∨ lab' = ⟨.twA, 5, lab.n⟩

@[expose] def GGTwE6SCFourOutKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L'),
          GGTwE6SCFourSetting I ψ A a₀ J₁ →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
            lab' = ⟨.D, 4, lab.n⟩ ∨ lab' = ⟨.triD4, 0, lab.n⟩ ∨ lab' = ⟨.A, 2, 3 * lab.n⟩ ∨
              lab' = ⟨.twA, 2, 3 * lab.n⟩) →
          ∃ a ∈ A, GGOutsideInndiag J₁ a

@[expose] def GGTwE6A5KKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (A : Subgroup (MulAut L')) (a₀ : MulAut L') (J₁ : Subgroup L'),
          GGTwE6SCFourSetting I ψ A a₀ J₁ →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, lab.n⟩) →
          ¬ GGUnitaryCommLifts J₁ lab.n 6 (A : Set (MulAut L'))

@[expose] def GGTwE6A5LKnown : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ (B' : Subgroup (MulAut L')) (s : MulAut L') (n : ℕ), IsElemAbelian 3 B' →
          (∀ a ∈ B', ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → s ∈ B' → s ≠ 1 →
          3 ^ 4 ≤ Nat.card B' → 3 ∣ 2 ^ n + 1 →
          ∀ J₁ : Subgroup L', IsComponentOf J₁ (ggFix s) → (∀ a ∈ B', ∀ l ∈ J₁, a l ∈ J₁) →
            LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩) →
            GGUnitaryCommLifts J₁ n 6 (B' : Set (MulAut L')) ∨
              (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨ GGTorusLift 3 5 R

end CFSG.StandardType

end

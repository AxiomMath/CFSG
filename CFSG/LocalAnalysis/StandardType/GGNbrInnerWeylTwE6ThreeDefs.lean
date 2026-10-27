module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylResidualTriD4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint

@[expose] def GGNbrWeylResidualTwE6Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylResidualOpenLabel p lab ∧ lab.tag = .twE6

@[expose] def GGNbrWeylResidualTriD4Label (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylResidualOpenLabel p lab ∧ lab.tag = .triD4

theorem ggNbrInnerWeylOn_residualOpen_of_split
    (hE : GGNbrInnerWeylOn GGNbrWeylResidualTwE6Label)
    (hD : GGNbrInnerWeylOn GGNbrWeylResidualTriD4Label) :
    GGNbrInnerWeylOn GGNbrWeylResidualOpenLabel :=
  (hE.or hD).mono fun _ _ h => by
    rcases h.1.2 with ⟨ht, -, -⟩ | ⟨ht, -, -⟩
    · exact Or.inl ⟨h, ht⟩
    · exact Or.inr ⟨h, ht⟩

@[expose] def GGTwoLocalAut {L' : Type} [Group L'] (E : Subgroup (MulAut L')) : Prop :=
  ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ e ∈ E, ∀ u ∈ U, e u ∈ U

@[expose] def GGTwoLocalLift (p r s : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ a : MulAut L', a ^ p = 1 →
      (∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
      a ∉ (MulAut.conj : L' →* MulAut L').range →
      ∃ E : Subgroup (MulAut L'),
        E ≤ Subgroup.zpowers a ⊔ (MulAut.conj : L' →* MulAut L').range ∧
        IsElemAbelian p E ∧ GGTwoLocalAut E ∧ p ^ r ≤ Nat.card E ∧
        ((¬ ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) → p ^ s ≤ Nat.card E)

@[expose] def GGHeisFieldComp (p r : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → p ∣ Nat.card ψ.ker →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
      (∃ a ∈ A, ¬ ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      Nat.card A = p ^ r → GGTorusSelfCent p A →
      ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a₀ l)) → GGFixCompCyclic p a₀ →
        ∃ n : L', GGTorusWeylElt p A n ∧
          (MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀ ∨
            (n * (a₀ n)⁻¹ ∈ Subgroup.center L' ∧ n * (a₀ n)⁻¹ ≠ 1))

@[expose] def GGNbrKGTwE6ThreeAddInn : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → GGTorusNoLineComp 3 4 (TwE6Delta.RecipeR K n) (Set.range MulAut.conj)

@[expose] def GGNbrKGTwE6ThreeAddFive : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n + 1 → GGTorusNoLineComp 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGNbrKGTwE6ThreeAddTwoLocal : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTwoLocalLift 3 5 6 R I F

@[expose] def GGNbrKGFieldTwE6ThreeAdd : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusNoLineFieldComp 3 5 R I F

@[expose] def GGNbrKGFieldTwE6ThreeAddHeis : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGHeisFieldComp 3 5 R I F

@[expose] def GGNbrKGFieldTwE6ThreeAddLiftFix : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twE6 → 3 ∣ 2 ^ lab.n + 1 →
    LargeEvenLabelAll lab fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGTorusLiftFix 3 4 R I F

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45KGLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag ≠ .E8 ∨ (p ≠ 3 ∧ p ≠ 5)) ∧
    ((lab.tag ≠ .F4 ∧ lab.tag ≠ .twF4 ∧ lab.tag ≠ .twF4der ∧ lab.tag ≠ .triD4) ∨ p ≠ 3)

@[expose] def GGL45IsPElt (p : ℕ) {M : Type*} [Monoid M] (α : M) : Prop := ∃ k : ℕ, α ^ p ^ k = 1

@[expose] def GGL45InducesIn {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (α : MulAut K) : Prop :=
  ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => k' = α k) φ

@[expose] def GGL45InS (p : ℕ) {K : Type*} [Group K] (E : Subgroup (MulAut K)) (h : K) : Prop :=
  GGL45IsPElt p h ∧ ∀ e ∈ E, e h = h

@[expose] def GGL45InP (p : ℕ) {K : Type*} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (I : Set (MulAut R)) (E : Subgroup (MulAut K))
    (α : MulAut K) : Prop :=
  GGL45IsPElt p α ∧ (∀ e ∈ E, α * e = e * α) ∧ GGL45InducesIn θ I α

@[expose] def GGL45TorusPackage (p : ℕ) {K : Type*} [Group K] {R : Type} [Group R]
    (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∃ k : ℕ, ¬ p ∣ k ∧
    (∀ α β : MulAut K, GGL45InP p θ I E α → GGL45InP p θ I E β → α * β = β * α) ∧
    (∀ α : MulAut K, GGL45InP p θ I E α → ψ * α * ψ⁻¹ = α ^ (1 + p ^ (s - 1) * k)) ∧
    (∀ h t : K, GGL45InS p E h → GGL45InS p E t → h * t = t * h ∧ GGL45IsPElt p (h * t)) ∧
    (∀ h : K, GGL45InS p E h → h ^ p ^ s = 1) ∧
    (∃ h : K, GGL45InS p E h ∧ h ^ p ^ (s - 1) ∉ Subgroup.center K) ∧
    (∀ α : MulAut K, GGL45InP p θ I E α → ∀ h : K, GGL45InS p E h → α h = h) ∧
    (∃ a₁ a₂ : K, GGL45InS p E a₁ ∧ GGL45InS p E a₂ ∧
      (a₁ * (ψ⁻¹ a₁)⁻¹) ^ p = 1 ∧ (a₂ * (ψ⁻¹ a₂)⁻¹) ^ p = 1 ∧
      a₁ * (ψ⁻¹ a₁)⁻¹ ∉ Subgroup.center K ∧
      ∀ i j : ℕ, (a₁ * (ψ⁻¹ a₁)⁻¹) ^ i * (a₂ * (ψ⁻¹ a₂)⁻¹) ^ j = 1 → p ∣ i ∧ p ∣ j) ∧
    ∀ γ : MulAut K, GGL45IsPElt p γ → (∀ e ∈ E, γ * e = e * γ) → ¬ GGL45InducesIn θ I γ →
      GGL45InducesIn θ I (γ ^ p) →
      ∃ k' : ℕ, ¬ p ∣ k' ∧ ∀ h : K, GGL45InS p E h → γ h = h ^ (1 + p ^ (s - 1) * k')

@[expose] def GGL45TorusKGRaw (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R),
    commutator K = ⊤ →
    (GGLabelA2 lab → p = 3 → p ∣ Nat.card (Subgroup.center K)) →
    ∀ (ψ : MulAut K) (E : Subgroup (MulAut K)), ψ ^ p = 1 →
      (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹)) →
      IsElemAbelian p E → p ^ 2 ≤ Nat.card E →
      (lab.tag = .D → lab.rank = 4 → p = 3 → p ^ 3 ≤ Nat.card E) →
      (∀ e ∈ E, GGL45InducesIn θ I e) → (∀ e ∈ E, e * ψ = ψ * e) →
      (∀ k : K, k ^ p = 1 → (∀ e ∈ E, e k = k) → ψ k = k → MulAut.conj k ∈ E) →
      (∀ R₀ Q : Subgroup K, IsElemAbelian p R₀ → (∀ r ∈ R₀, ψ r = r) → IsPGroup 2 Q →
        Q ≠ ⊥ → (∀ g ∈ Q, ψ g ∈ Q) → R₀ ≤ Subgroup.normalizer (Q : Set K) →
        Nat.card R₀ * p ≤ Nat.card E * p ^ 2 ∧
          (Nat.Coprime p (Nat.card (Subgroup.center K)) → Nat.card R₀ ≤ Nat.card E)) →
      (∃ P : Subgroup (MulAut K), P ≤ E ∧ Nat.card E ≤ p * Nat.card P ∧ ∀ e ∈ P,
        ∃ γ : MulAut K, GGL45IsPElt p γ ∧ (∀ e' ∈ E, γ * e' = e' * γ) ∧
          IsPGroup p (Subgroup.closure (insert γ (insert ψ (E : Set (MulAut K))))) ∧
          e = γ * ψ⁻¹ * γ⁻¹ * ψ) →
      GGL45TorusPackage p I θ ψ E

@[expose] def GGL45TorusKnownForms : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGL45KGLabel p lab → LargeEvenLabelAll lab (GGL45TorusKGRaw p lab)

@[expose] def GGL45TorsionTag (lab : LargeEvenLabel) : Prop :=
  lab.tag = .E8 ∨ lab.tag = .F4 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der

@[expose] def GGStdSubNotTorsionInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp p B x L → LargeEvenStdSub p B x L D J →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGL45TorsionTag lab)

@[expose] def GGL45FieldFixKGRaw (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F =>
    (GGLabelA2 lab → p = 3 → ∀ A : Subgroup (MulAut R), IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 3) ∧
    ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
      ∀ ψ : MulAut K, ψ ^ p = 1 →
      (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
        LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹)) →
      ∀ Q : Subgroup K, IsComponentOf Q (ggAutFixedSubgroup ψ) →
        (GGL45TorsionTag lab → LargeEvenMarking Q fun lab' _ _ _ _ _ => GGL45TorsionTag lab') ∧
        (GGLabelA2 lab → p = 3 → ¬ p ∣ Nat.card (Subgroup.center K) →
          Subgroup.center Q = ⊥ ∧ LargeEvenMarking Q fun lab' _ _ _ _ _ => GGLabelA2 lab')

@[expose] def GGL45FieldFixKnownForms : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (GGL45FieldFixKGRaw p lab)

@[expose] def GGL45KnownForms : Prop :=
  GGL45TorusKnownForms ∧ GGL45FieldFixKnownForms

end CFSG.StandardType

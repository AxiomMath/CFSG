module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Facts

variable (p : ℕ) {K : Type*} [Group K] {R : Type} [Group R]

@[expose] def GGL45InCIp (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) (u : MulAut R) : Prop :=
  u ∈ I ∧ (∀ e ∈ E, u * ggInducedAut θ e = ggInducedAut θ e * u) ∧ GGL45IsPElt p u

@[expose] def GGL45HOne (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) (f : MulAut R) (s : ℕ) (c : ℤ) : Prop :=
  (∀ u v : MulAut R, GGL45InCIp p I θ E u → GGL45InCIp p I θ E v → u * v = v * u) ∧
    ∀ u : MulAut R, GGL45InCIp p I θ E u → u ^ p ^ s = 1 ∧ f * u * f⁻¹ = u ^ c

@[expose] def GGL45HTwo (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) (s : ℕ) (c : ℤ) : Prop :=
  (∀ h t : K, GGL45InS p E h → GGL45InS p E t → h * t = t * h) ∧
    (∀ h : K, GGL45InS p E h → h ^ p ^ s = 1 ∧ ψ h = h ^ c) ∧
    ∀ α : MulAut K, GGL45InducesIn θ I α → (∀ e ∈ E, α * e = e * α) →
      ∀ h : K, GGL45InS p E h → α h = h

@[expose] def GGL45HThree (E : Subgroup (MulAut K)) (s : ℕ) : Prop :=
  (∃ h : K, GGL45InS p E h ∧ h ^ p ^ (s - 1) ∉ Subgroup.center K) ∧
    ∃ b₁ b₂ : K, (∃ h : K, GGL45InS p E h ∧ b₁ = h ^ p ^ (s - 1)) ∧
      (∃ h : K, GGL45InS p E h ∧ b₂ = h ^ p ^ (s - 1)) ∧ b₁ ∉ Subgroup.center K ∧
      ∀ i j : ℕ, b₁ ^ i * b₂ ^ j = 1 → p ∣ i ∧ p ∣ j

@[expose] def GGL45HFour (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) : Prop :=
  ∃ T : Subgroup (MulAut R), (∀ u ∈ I, u ∈ T) ∧ (∃ g ∈ T, ∀ x ∈ T, ∃ k : ℤ, g ^ k * x ∈ I) ∧
    ∀ α : MulAut R, GGL45IsPElt p α →
      (∀ e ∈ E, α * ggInducedAut θ e = ggInducedAut θ e * α) → α ∈ T

@[expose] def GGL45HFourMod (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) (f : MulAut R) : Prop :=
  ∀ α : MulAut R, GGL45IsPElt p α → (∀ e ∈ E, α * ggInducedAut θ e = ggInducedAut θ e * α) →
    α ∉ I → α ^ p ∈ I → ∃ j : ℕ, ¬ p ∣ j ∧ α * (f ^ j)⁻¹ ∈ I

@[expose] def GGL45TorusH (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∃ c : ℤ, ∃ k : ℕ, ¬ p ∣ k ∧
    c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s] ∧
    GGL45HOne p I θ E (ggInducedAut θ ψ) s c ∧ GGL45HTwo p I θ ψ E s c ∧ GGL45HThree p E s ∧
    GGL45HFourMod p I θ E (ggInducedAut θ ψ)

end Facts

@[expose] def GGL45TorusKGHyp (p : ℕ) (lab : LargeEvenLabel) {R : Type} [Group R]
    (I F : Set (MulAut R)) {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) : Prop :=
  ψ ^ p = 1 ∧
    (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
      LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹)) ∧
    IsElemAbelian p E ∧ p ^ 2 ≤ Nat.card E ∧
    (lab.tag = .D → lab.rank = 4 → p = 3 → p ^ 3 ≤ Nat.card E) ∧
    (∀ e ∈ E, GGL45InducesIn θ I e) ∧ (∀ e ∈ E, e * ψ = ψ * e) ∧
    (∀ k : K, k ^ p = 1 → (∀ e ∈ E, e k = k) → ψ k = k → MulAut.conj k ∈ E) ∧
    (∀ R₀ Q : Subgroup K, IsElemAbelian p R₀ → (∀ r ∈ R₀, ψ r = r) → IsPGroup 2 Q →
      Q ≠ ⊥ → (∀ g ∈ Q, ψ g ∈ Q) → R₀ ≤ Subgroup.normalizer (Q : Set K) →
      Nat.card R₀ * p ≤ Nat.card E * p ^ 2 ∧
        (Nat.Coprime p (Nat.card (Subgroup.center K)) → Nat.card R₀ ≤ Nat.card E)) ∧
    (∃ P : Subgroup (MulAut K), P ≤ E ∧ Nat.card E ≤ p * Nat.card P ∧ ∀ e ∈ P,
      ∃ γ : MulAut K, GGL45IsPElt p γ ∧ (∀ e' ∈ E, γ * e' = e' * γ) ∧
        IsPGroup p (Subgroup.closure (insert γ (insert ψ (E : Set (MulAut K))))) ∧
        e = γ * ψ⁻¹ * γ⁻¹ * ψ)

theorem ggL45TorusKGRaw_iff_hyp (p : ℕ) (lab : LargeEvenLabel) (R : Type) [Group R]
    (I F : Set (MulAut R)) :
    GGL45TorusKGRaw p lab R I F ↔
      ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
        (GGLabelA2 lab → p = 3 → p ∣ Nat.card (Subgroup.center K)) →
        ∀ (ψ : MulAut K) (E : Subgroup (MulAut K)), GGL45TorusKGHyp p lab I F θ ψ E →
          GGL45TorusPackage p I θ ψ E := by
  constructor
  · intro h K _ _ θ hK hA ψ E hH
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hH
    exact h K θ hK hA ψ E h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  · intro h K _ _ θ hK hA ψ E h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact h K θ hK hA ψ E ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

@[expose] def GGL45TorusHRaw (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R),
    commutator K = ⊤ →
    (GGLabelA2 lab → p = 3 → p ∣ Nat.card (Subgroup.center K)) →
    ∀ (ψ : MulAut K) (E : Subgroup (MulAut K)), GGL45TorusKGHyp p lab I F θ ψ E →
      GGL45TorusH p I θ ψ E

@[expose] def GGL45TorusHKnownFormsOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGL45KGLabel p lab → S p lab → LargeEvenLabelAll lab (GGL45TorusHRaw p lab)

section Basic

variable {K : Type*} [Group K] {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R)

theorem ggL45_largeEvenInduces_inducedAut (α : MulAut K) :
    LargeEvenInduces θ (fun k k' => k' = α k) (ggInducedAut θ α) := by
  intro l l' h
  subst h
  exact ggInducedAut_apply θ α l

theorem ggL45_inducesIn_iff (I : Set (MulAut R)) (α : MulAut K) :
    GGL45InducesIn θ I α ↔ ggInducedAut θ α ∈ I := by
  constructor
  · rintro ⟨φ, hφ, hind⟩
    have : φ = ggInducedAut θ α := by
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      induction q using QuotientGroup.induction_on with
      | H l => rw [ggInducedAut_apply]; exact hind l _ rfl
    rwa [this] at hφ
  · intro h
    exact ⟨_, h, ggL45_largeEvenInduces_inducedAut θ α⟩

end Basic

end CFSG.StandardType

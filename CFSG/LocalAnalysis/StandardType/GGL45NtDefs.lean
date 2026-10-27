module

public import CFSG.LocalAnalysis.StandardType.GGL45TorusHForms
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45NtCIp (p : ℕ) {R : Type} [Group R] (I : Set (MulAut R))
    (Ebar : Subgroup (MulAut R)) (u : MulAut R) : Prop :=
  u ∈ I ∧ (∀ e ∈ Ebar, u * e = e * u) ∧ GGL45IsPElt p u

@[expose] def GGL45NtCore (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    ∀ (Ebar : Subgroup (MulAut R)) (f' : MulAut R),
    IsElemAbelian p Ebar → p ^ 2 ≤ Nat.card Ebar → (∀ e ∈ Ebar, e ∈ I) →
    f' ^ p = 1 → (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧ f' = u * f * u⁻¹) →
    (∀ e ∈ Ebar, e * f' = f' * e) →
    (∀ r : R, r ^ p = 1 → (∀ e ∈ Ebar, e r = r) → f' r = r → MulAut.conj r ∈ Ebar) →
    ∃ s : ℕ, 2 ≤ s ∧ ∃ (c : ℤ) (k : ℕ), ¬ p ∣ k ∧
      c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s] ∧
      (∀ u v : MulAut R, GGL45NtCIp p I Ebar u → GGL45NtCIp p I Ebar v → u * v = v * u) ∧
      (∀ u : MulAut R, GGL45NtCIp p I Ebar u → u ^ p ^ s = 1 ∧ f' * u * f'⁻¹ = u ^ c) ∧
      (∀ u : MulAut R, GGL45NtCIp p I Ebar u → ∀ w ∈ I, (∀ e ∈ Ebar, w * e = e * w) →
        w * u = u * w) ∧
      ∃ a₁ a₂ : MulAut R, GGL45NtCIp p I Ebar a₁ ∧ GGL45NtCIp p I Ebar a₂ ∧
        ∀ i j : ℕ, (a₁ ^ p ^ (s - 1)) ^ i * (a₂ ^ p ^ (s - 1)) ^ j = 1 → p ∣ i ∧ p ∣ j

@[expose] def GGL45NtRec (p : ℕ) : LargeEvenRawCont :=
  fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    (∀ r : R, MulAut.conj r ∈ I) ∧
      (∀ u ∈ I, GGL45IsPElt p u → ∃ r : R, u = MulAut.conj r) ∧ GGCenterPrime p R

@[expose] def GGL45NtAut (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    (∃ J : Subgroup (MulAut R), J.Normal ∧ (J : Set (MulAut R)) = I) ∧
      ∀ α : MulAut R, GGL45IsPElt p α → α ∉ I → α ^ p ∈ I →
        ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ α * (f ^ j)⁻¹ ∈ I

@[expose] def GGL45NtVac (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => (∀ f ∈ F, orderOf f ≠ p) ∨
    ¬ ∃ A : Subgroup (MulAut R), IsElemAbelian p A ∧ p ^ 2 ≤ Nat.card A ∧ ∀ a ∈ A, a ∈ I

@[expose] def GGL45TorusH123 (p : ℕ) {K : Type*} [Group K] {R : Type} [Group R]
    (I : Set (MulAut R)) (θ : K ⧸ Subgroup.center K ≃* R) (ψ : MulAut K)
    (E : Subgroup (MulAut K)) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ ∃ c : ℤ, ∃ k : ℕ, ¬ p ∣ k ∧
    c ≡ 1 + (p : ℤ) ^ (s - 1) * k [ZMOD (p : ℤ) ^ s] ∧
    GGL45HOne p I θ E (ggInducedAut θ ψ) s c ∧ GGL45HTwo p I θ ψ E s c ∧ GGL45HThree p E s

@[expose] def GGL45H4Raw (p : ℕ) (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I F => ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R),
    commutator K = ⊤ → ∀ (ψ : MulAut K) (E : Subgroup (MulAut K)),
      GGL45TorusKGHyp p lab I F θ ψ E → GGL45HFourMod p I θ E (ggInducedAut θ ψ)

@[expose] def GGL45NtSimp : LargeEvenRawCont :=
  fun R _ _ _ => (∃ a b : R, a * b ≠ b * a) → IsSimpleGroup R

@[expose] def GGL45NtOn (S : ℕ → LargeEvenLabel → Prop)
    (P : ℕ → LargeEvenLabel → LargeEvenRawCont) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    GGL45KGLabel p lab → S p lab → LargeEvenLabelAll lab (P p lab)

@[expose] def GGL45NtSimpOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun _ _ => GGL45NtSimp

@[expose] def GGL45NtRecOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun p _ => GGL45NtRec p
@[expose] def GGL45NtCoreOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun p _ => GGL45NtCore p
@[expose] def GGL45NtAutOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun p _ => GGL45NtAut p
@[expose] def GGL45NtVacOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S fun p _ => GGL45NtVac p
@[expose] def GGL45NtH4On (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  GGL45NtOn S GGL45H4Raw

@[expose] def GGL45NtVacLabel (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ lab.rank = 1) ∨ (lab.tag = .twD ∧ lab.rank = 2) ∨ lab.tag = .twB2 ∨
    lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der

@[expose] def GGL45NtExcLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
    lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4

@[expose] def GGL45NtFamVac (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45FamNonTorsion p lab ∧ GGL45NtVacLabel lab
@[expose] def GGL45NtFamCl (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45FamNonTorsion p lab ∧ ¬ GGL45NtVacLabel lab ∧ ¬ GGL45NtExcLabel lab
@[expose] def GGL45NtFamEx (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45FamNonTorsion p lab ∧ ¬ GGL45NtVacLabel lab ∧ GGL45NtExcLabel lab
@[expose] def GGL45NtD43 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45FamNonTorsion p lab ∧ lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
@[expose] def GGL45NtFamClAut (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamCl p lab ∧ ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3)

@[expose] def GGL45NtLinLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3)
@[expose] def GGL45NtUniLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3)
@[expose] def GGL45NtSpLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .B ∨ lab.tag = .C
@[expose] def GGL45NtFamLin (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamCl p lab ∧ GGL45NtLinLabel lab
@[expose] def GGL45NtFamUni (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamCl p lab ∧ GGL45NtUniLabel lab
@[expose] def GGL45NtFamSp (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamCl p lab ∧ GGL45NtSpLabel lab
@[expose] def GGL45NtFamOrth (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamCl p lab ∧ ¬ GGL45NtLinLabel lab ∧ ¬ GGL45NtUniLabel lab ∧ ¬ GGL45NtSpLabel lab
@[expose] def GGL45NtFamExU (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamEx p lab ∧ (lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
@[expose] def GGL45NtFamExE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamEx p lab ∧ lab.tag = .E6
@[expose] def GGL45NtFamExTwE6 (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamEx p lab ∧ lab.tag = .twE6
@[expose] def GGL45NtFamExTw (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGL45NtFamEx p lab ∧ (lab.tag = .triD4 ∨ lab.tag = .twF4)

theorem GGL45NtOn.mono {S : ℕ → LargeEvenLabel → Prop}
    {P P' : ℕ → LargeEvenLabel → LargeEvenRawCont}
    (hPP : ∀ (p : ℕ), p.Prime → ∀ (lab : LargeEvenLabel) (R : Type) [Group R]
      (I F : Set (MulAut R)), P p lab R I F → P' p lab R I F)
    (h : GGL45NtOn S P) : GGL45NtOn S P' :=
  fun p hp hp2 lab hlab hkg hS => (h p hp hp2 lab hlab hkg hS).mono (hPP p hp lab)

theorem GGL45NtOn.and {S : ℕ → LargeEvenLabel → Prop}
    {P P' : ℕ → LargeEvenLabel → LargeEvenRawCont} (h : GGL45NtOn S P) (h' : GGL45NtOn S P') :
    GGL45NtOn S fun p lab R _ I F => P p lab R I F ∧ P' p lab R I F :=
  fun p hp hp2 lab hlab hkg hS => largeEvenLabelAll_and (h p hp hp2 lab hlab hkg hS)
    (h' p hp hp2 lab hlab hkg hS)

theorem GGL45NtOn.antitone {S S' : ℕ → LargeEvenLabel → Prop}
    {P : ℕ → LargeEvenLabel → LargeEvenRawCont} (hSS : ∀ p lab, S' p lab → S p lab)
    (h : GGL45NtOn S P) : GGL45NtOn S' P :=
  fun p hp hp2 lab hlab hkg hS => h p hp hp2 lab hlab hkg (hSS p lab hS)

theorem GGL45NtOn.union {S₁ S₂ : ℕ → LargeEvenLabel → Prop}
    {P : ℕ → LargeEvenLabel → LargeEvenRawCont} (h₁ : GGL45NtOn S₁ P) (h₂ : GGL45NtOn S₂ P) :
    GGL45NtOn (fun p lab => S₁ p lab ∨ S₂ p lab) P :=
  fun p hp hp2 lab hlab hkg hS =>
    hS.elim (h₁ p hp hp2 lab hlab hkg) (h₂ p hp hp2 lab hlab hkg)

theorem ggL45NtFam_cover (p : ℕ) (lab : LargeEvenLabel) (h : GGL45FamNonTorsion p lab) :
    GGL45NtFamVac p lab ∨ GGL45NtFamCl p lab ∨ GGL45NtFamEx p lab := by
  by_cases hv : GGL45NtVacLabel lab
  · exact Or.inl ⟨h, hv⟩
  · by_cases he : GGL45NtExcLabel lab
    · exact Or.inr (Or.inr ⟨h, hv, he⟩)
    · exact Or.inr (Or.inl ⟨h, hv, he⟩)

theorem ggL45NtFamCl_split (p : ℕ) (lab : LargeEvenLabel) (h : GGL45NtFamCl p lab) :
    GGL45NtFamClAut p lab ∨ GGL45NtD43 p lab := by
  by_cases hd : lab.tag = .D ∧ lab.rank = 4 ∧ p = 3
  · exact Or.inr ⟨h.1, hd⟩
  · exact Or.inl ⟨h, hd⟩

theorem ggL45NtFamCl_cover (p : ℕ) (lab : LargeEvenLabel) (h : GGL45NtFamCl p lab) :
    GGL45NtFamLin p lab ∨ GGL45NtFamUni p lab ∨ GGL45NtFamSp p lab ∨ GGL45NtFamOrth p lab := by
  by_cases h1 : GGL45NtLinLabel lab
  · exact Or.inl ⟨h, h1⟩
  · by_cases h2 : GGL45NtUniLabel lab
    · exact Or.inr (Or.inl ⟨h, h2⟩)
    · by_cases h3 : GGL45NtSpLabel lab
      · exact Or.inr (Or.inr (Or.inl ⟨h, h3⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨h, h1, h2, h3⟩))

theorem ggL45NtFamEx_cover (p : ℕ) (lab : LargeEvenLabel) (h : GGL45NtFamEx p lab) :
    GGL45NtFamExU p lab ∨ GGL45NtFamExE6 p lab ∨ GGL45NtFamExTwE6 p lab ∨
      GGL45NtFamExTw p lab := by
  have h1 := h.2.2
  simp only [GGL45NtExcLabel] at h1
  rcases h1 with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact Or.inl ⟨h, Or.inl h1⟩
  · exact Or.inl ⟨h, Or.inr (Or.inl h1)⟩
  · exact Or.inr (Or.inl ⟨h, h1⟩)
  · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inl h1))⟩
  · exact Or.inl ⟨h, Or.inr (Or.inr (Or.inr h1))⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h, h1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, Or.inl h1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, Or.inr h1⟩))

theorem ggL45TorusH_of_parts {p : ℕ} {K : Type*} [Group K] {R : Type} [Group R]
    {I : Set (MulAut R)} {θ : K ⧸ Subgroup.center K ≃* R} {ψ : MulAut K}
    {E : Subgroup (MulAut K)} (h123 : GGL45TorusH123 p I θ ψ E)
    (h4 : GGL45HFourMod p I θ E (ggInducedAut θ ψ)) : GGL45TorusH p I θ ψ E := by
  obtain ⟨s, hs, c, k, hk, hc, H1, H2, H3⟩ := h123
  exact ⟨s, hs, c, k, hk, hc, H1, H2, H3, h4⟩

end CFSG.StandardType

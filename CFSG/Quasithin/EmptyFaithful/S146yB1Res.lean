module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank CFSG.Blueprint

@[expose] def Lemma115Type (K : Type) [Group K] : Prop :=
  (IsSimpleGroup K ∧ Lemma115LieCharTwo K) ∨
  (Subgroup.center K ≠ ⊥ ∧ Subgroup.center K = CFSG.pCore 2 K ∧ IsL34OrG24 (K ⧸ CFSG.pCore 2 K)) ∨
  (∃ _ : (K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 6),
    Nat.card (Subgroup.center K) = 1 ∨ Nat.card (Subgroup.center K) = 3) ∨
  (∃ _ : (K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 7),
    Nat.card (Subgroup.center K) = 1 ∨ Nat.card (Subgroup.center K) = 3) ∨
  (CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 3 3 1 ∨
    ∃ p : ℕ, IsFermatOrMersennePrime p ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel K .PSL 2 p 1) ∨
  ((∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧
    Nonempty ((K ⧸ CFSG.pCore 2 K) ≃* NativeSporadic.Carrier s)))

theorem lemma115Type_of_cases {G : Type} [Group G] {L : Subgroup G} {z : G}
    (h : Lemma115Cases L z) : Lemma115Type ↥L := by
  rcases h with ⟨hs, hl, -⟩ | ⟨h1, h2, h3, -⟩ | ⟨φ, σ, hc, -, -⟩ | ⟨φ, σ, hc, -, -⟩ | ⟨hm, -⟩ |
    ⟨hf, -⟩
  · exact Or.inl ⟨hs, hl⟩
  · exact Or.inr (Or.inl ⟨h1, h2, h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨φ, hc⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, hc⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hf))))

@[expose] def BorelAutFree : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (X B : Subgroup Γ) (n : ℕ) (g : Γ),
    (E2.IsBenderOf n ↥X ∨ (2 ≤ n ∧ (IsPSL 3 2 n ↥X ∨ E2.IsSp4Prime n ↥X))) →
    E2.IsBorelIn X B → g ∈ Subgroup.normalizer (X : Set Γ) → g ^ 2 = 1 →
    (∀ b ∈ B, g * b = b * g) → ∀ x ∈ X, g * x = x * g

@[expose] def L2PrimeOnList115 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Lemma115Type K →
    ∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 (K ⧸ Subgroup.center K) →
      p = 7 ∨ IsFermatOrMersennePrime p

@[expose] def L2SquareNotOnList115 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Lemma115Type K →
    ∀ p : ℕ, p.Prime → 3 < p → ¬ IsPSL 2 p 2 (K ⧸ Subgroup.center K)

@[expose] def U3OddNotOnList115 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Lemma115Type K →
    ∀ p : ℕ, p.Prime → p % 4 = 1 → ¬ IsPSU 3 p 1 (K ⧸ Subgroup.center K)

@[expose] def L3OddNotOnList115 : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.IsQuasisimple K → Lemma115Type K →
    ∀ p : ℕ, p.Prime → p % 4 = 3 → 3 < p → ¬ IsPSL 3 p 1 (K ⧸ Subgroup.center K)

@[expose] def L3TwoParabolicAut : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (Ts Ks P : Subgroup Γ), IsPGroup 2 Ts → IsPSL 3 2 1 ↥Ks →
    IsMaxParabolic2 Ks P →
    Ts ⊓ Subgroup.normalizer (Ks : Set Γ) ≤ Subgroup.normalizer (P : Set Γ) → E2.autCard Ts Ks ≤ 8

structure B1Residues : Prop where
  borel : BorelAutFree
  l2Prime : L2PrimeOnList115
  l2Square : L2SquareNotOnList115
  u3Odd : U3OddNotOnList115
  l3Odd : L3OddNotOnList115
  l3Two : L3TwoParabolicAut

end CFSG.Quasithin

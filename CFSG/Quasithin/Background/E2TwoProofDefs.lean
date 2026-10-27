module

public import CFSG.Quasithin.Background.B69Num

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace E2P

variable {X : Type} [Group X]

@[expose] def zOf (S : Subgroup X) : Subgroup X := S ⊓ Subgroup.centralizer (S : Set X)

structure ASHyp [Finite X] (K T M : Subgroup X) : Prop where
  minPar : MinParabolic (⊤ : Subgroup X) T M
  normal : K.Normal
  simple : IsSimpleGroup ↥K
  nonab : ∃ a b : ↥K, a * b ≠ b * a
  sup : K ⊔ T = ⊤
  cent : Subgroup.centralizer (K : Set X) = ⊥

@[expose] def ASCases (K T M : Subgroup X) : Prop :=
  (∃ n : ℕ, E2.IsBenderOf n ↥K ∧ E2.IsBorelIn K (M ⊓ K)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ (IsPSL 3 2 n ↥K ∨ E2.IsSp4Prime n ↥K) ∧
    E2.IsDiagramNontrivial T K (T ⊓ K) ∧ E2.IsBorelIn K (M ⊓ K)) ∨
  (∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
    IsPSL 2 p e ↥K ∧ M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) ∧
    8 < E2.autCard T K) ∨
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥K) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥K ∧ E2.InducesOuter T K)) ∧
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X))

@[expose] def E22AltFam : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T M : Subgroup X), ASHyp K T M →
    ((IsAlt 5 ↥K ∨ IsPSL 2 5 1 ↥K) → IsPSL 2 2 2 ↥K ∧ E2.IsBorelIn K (M ⊓ K)) ∧
    ((IsAlt 6 ↥K ∨ IsPSL 2 3 2 ↥K) → E2.IsSp4Prime 1 ↥K ∧ E2.IsDiagramNontrivial T K (T ⊓ K) ∧
      E2.IsBorelIn K (M ⊓ K)) ∧
    ¬ IsAlt 7 ↥K ∧ ¬ IsAlt 8 ↥K

@[expose] def E22BenderFam : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T M : Subgroup X), ASHyp K T M →
    ∀ n : ℕ, E2.IsBenderOf n ↥K → E2.IsBorelIn K (M ⊓ K)

@[expose] def E22L3Sp4Fam : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T M : Subgroup X), ASHyp K T M →
    ∀ n : ℕ, 1 ≤ n → (IsPSL 3 2 n ↥K ∨ E2.IsSp4Prime n ↥K) →
      E2.IsDiagramNontrivial T K (T ⊓ K) ∧ E2.IsBorelIn K (M ⊓ K)

@[expose] def E22Char2ExcFam : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T M : Subgroup X), ASHyp K T M →
    ((∃ f : ℕ, 2 ≤ f ∧ IsG2 2 f ↥K) ∨ (∃ f : ℕ, 1 ≤ f ∧ Is3D4 2 f ↥K) ∨
      (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ Is2F4 f ↥K) ∨ IsTits ↥K) → False

@[expose] def E22LnTwoFam : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T M : Subgroup X), ASHyp K T M →
    ∀ n : ℕ, (n = 4 ∨ n = 5) → IsPSL n 2 1 ↥K → False

@[expose] def E22OddL2Fam : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K T M : Subgroup X), ASHyp K T M →
    ∀ p f : ℕ, p.Prime → p ≠ 2 → (f = 1 ∨ f = 2) → p ^ f ≠ 5 → p ^ f ≠ 9 →
      IsPSL 2 p f ↥K →
      3 < p ∧ (p ^ f % 8 = 1 ∨ p ^ f % 8 = 7) ∧
        M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) ∧ 8 < E2.autCard T K

@[expose] def Asc80L3Eps : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (H : Type) [Group H] [Finite H] (K T M : Subgroup H),
    K.Normal → IsSimpleGroup ↥K → (IsPSL 3 p 1 ↥K ∨ IsPSU 3 p 1 ↥K) →
    Subgroup.centralizer (K : Set H) = ⊥ → CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ →
    K ⊔ T = ⊤ → IsUniqueMaxOver ⊤ T M →
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set H) ∧
      ((IsPSL 3 p 1 ↥K ∧ p % 4 = 3 ∧ E2.InducesOuter T K) ∨ (IsPSU 3 p 1 ↥K ∧ p % 4 = 1))

@[expose] def SporTen (s : TauCeti.SporadicName) : Prop :=
  s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .HS ∨
    s = .He ∨ s = .Ru

@[expose] def Asc86bClauseB (s : TauCeti.SporadicName) : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (K T : Subgroup H), K.Normal → IsSporadic s ↥K →
    Subgroup.centralizer (K : Set H) = ⊥ → CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → K ⊔ T = ⊤ →
    ∃ M₁ M₂ : Subgroup H, IsMaxSubgroupIn ⊤ M₁ ∧ IsMaxSubgroupIn ⊤ M₂ ∧ M₁ ≠ M₂ ∧ T ≤ M₁ ∧
      T ≤ M₂

@[expose] def E22SporTenFam : Prop := ∀ s : TauCeti.SporadicName, SporTen s → Asc86bClauseB s

@[expose] def Asc86bSporadic : Prop := Asc86bClauseB .J4

structure E22Families : Prop where
  alt : E22AltFam
  bender : E22BenderFam
  l3sp4 : E22L3Sp4Fam
  char2Exc : E22Char2ExcFam
  lnTwo : E22LnTwoFam
  oddL2 : E22OddL2Fam
  asc80 : Asc80L3Eps
  sporTen : E22SporTenFam
  asc86b : Asc86bSporadic

@[expose] def E22ListStatement : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M : Subgroup Γ), MinParabolic H T M → SQTKGroup ↥H →
    ¬ Group.IsSolvable ↥H →
    ∃ K : Subgroup Γ, K ∈ cComp H ∧ H = K ⊔ T ∧
      CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) ∧ B69.E22Fam ↥(E2.star M H K)

end E2P

end CFSG.Quasithin

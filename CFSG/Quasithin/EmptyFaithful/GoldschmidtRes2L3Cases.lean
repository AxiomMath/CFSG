module

public import CFSG.Quasithin.Background.E2TwoNoNStmt
public import CFSG.Quasithin.Background.E2TwoCLie

public section

namespace CFSG.Quasithin.Gap6R2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {Γ : Type} [Group Γ]

@[expose] def E22Case1b (H T M K : Subgroup Γ) : Prop :=
  let Ks := E2.star M H K
  let MKs := E2.star M H (M ⊓ K)
  let TKs := E2.star M H (T ⊓ K)
  let Ts := E2.star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (E2.StarQuot M H))
  kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
    ∃ p : ℕ, p.Prime ∧ (p % 8 = 1 ∨ p % 8 = 7) ∧ IsPSL 2 p 1 ↥Ks ∧
      MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (E2.StarQuot M H)) ∧ 8 < E2.autCard Ts Ks

@[expose] def E22Case2c (H T M K : Subgroup Γ) : Prop :=
  let Ks := E2.star M H K
  let MKs := E2.star M H (M ⊓ K)
  let TKs := E2.star M H (T ⊓ K)
  let Ts := E2.star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (E2.StarQuot M H))
  T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ∃ p e : ℕ, p.Prime ∧ 3 < p ∧ (e = 1 ∨ e = 2) ∧ (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) ∧
      IsPSL 2 p e ↥Ks ∧ MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (E2.StarQuot M H)) ∧
      8 < E2.autCard Ts Ks

@[expose] def E22Case2d (H T M K : Subgroup Γ) : Prop :=
  let Ks := E2.star M H K
  let MKs := E2.star M H (M ⊓ K)
  let TKs := E2.star M H (T ⊓ K)
  let Ts := E2.star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (E2.StarQuot M H))
  T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ E2.InducesOuter Ts Ks)) ∧
      MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (E2.StarQuot M H))

@[expose] def E22Rest (H T M K : Subgroup Γ) : Prop :=
  E22Case1b H T M K ∨ E22Case2d H T M K

@[expose] def E22Case2bOne (H T M K : Subgroup Γ) : Prop :=
  T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ pCoreOf 2 H ∧
      ∀ y ∈ K ⊔ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H) ∧
    (IsPSL 3 2 1 ↥(E2.star M H K) ∨ E2.IsSp4Prime 1 ↥(E2.star M H K)) ∧
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K))

theorem e22Cases_cases {H T M K : Subgroup Γ} (h : E2.E22CasesNoN H T M K) :
    E2.E22LieCases H T M K ∨ E22Case2bOne H T M K ∨ E22Case2c H T M K ∨ E22Rest H T M K := by
  unfold E2.E22CasesNoN at h
  dsimp only at h
  unfold E2.E22LieCases E22Case2bOne E22Rest E22Case1b E22Case2c E22Case2d
  dsimp only
  rcases h with ⟨hker, t, ht, hne, hMeq, h1⟩ | ⟨hTN, hker2, h2⟩
  · rcases h1 with ⟨n, hn, hty, hB⟩ | h1b
    · exact Or.inl (Or.inl ⟨hker, t, ht, hne, hMeq, n, hn, hty, hB⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hker, t, ht, hne, hMeq, h1b⟩)))
  · rcases h2 with ⟨n, hBen, hB⟩ | ⟨n, hn1, hty, hdiag, hB⟩ | h2c | h2d
    · exact Or.inl (Or.inr ⟨hTN, hker2, Or.inl ⟨n, hBen, hB⟩⟩)
    · by_cases hn : n = 1
      · subst hn
        exact Or.inr (Or.inl ⟨hTN, hker2, hty, hB⟩)
      · refine Or.inl (Or.inr ⟨hTN, hker2, Or.inr ⟨n, by omega, ?_, hdiag, hB⟩⟩)
        rcases hty with h | h
        · exact Or.inl h
        · right
          simp only [E2.IsSp4Prime, hn, ↓reduceIte] at h
          exact h
    · exact Or.inr (Or.inr (Or.inl ⟨hTN, hker2, h2c⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hTN, hker2, h2d⟩)))

end CFSG.Quasithin.Gap6R2

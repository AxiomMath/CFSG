module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {Γ : Type} [Group Γ]

@[expose] def E22LieCases (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  (kerIn M H = Q ∧ ∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T ∧
    ∃ n : ℕ, 2 ≤ n ∧ (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) ∧ IsBorelIn Ks MKs) ∨
  (T ≤ Subgroup.normalizer (K : Set Γ) ∧
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) ∧
    ((∃ n : ℕ, IsBenderOf n ↥Ks ∧ IsBorelIn Ks MKs) ∨
      (∃ n : ℕ, 2 ≤ n ∧ (IsPSL 3 2 n ↥Ks ∨ IsPSp4 2 n ↥Ks) ∧ IsDiagramNontrivial Ts Ks TKs ∧
        IsBorelIn Ks MKs)))

theorem E22LieCases.exists_borel {H T M K : Subgroup Γ} (h : E22LieCases H T M K) :
    ∃ n : ℕ, 2 ≤ n ∧ (IsBenderOf n ↥(star M H K) ∨ IsPSL 3 2 n ↥(star M H K) ∨
        IsPSp4 2 n ↥(star M H K)) ∧
      IsBorelIn (star M H K) (star M H (M ⊓ K)) := by
  dsimp only [E22LieCases] at h
  rcases h with ⟨-, -, -, -, -, n, hn, hty, hB⟩ | ⟨-, -, ⟨n, hBen, hB⟩ | ⟨n, hn, hty, -, hB⟩⟩
  · exact ⟨n, hn, Or.inl ⟨hn, hty.elim Or.inl fun h => Or.inr (Or.inl h)⟩, hB⟩
  · exact ⟨n, hBen.1, Or.inl hBen, hB⟩
  · exact ⟨n, hn, Or.inr hty, hB⟩

end E2

end CFSG.Quasithin

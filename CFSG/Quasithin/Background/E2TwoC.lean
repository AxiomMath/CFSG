module

public import CFSG.Quasithin.Background.E2TwoNoNStmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace E2

variable {Γ : Type} [Group Γ]

@[expose] def E22NParamCases (H T M K : Subgroup Γ) : Prop :=
  let Ks := star M H K
  let MKs := star M H (M ⊓ K)
  let TKs := star M H (T ⊓ K)
  let Ts := star M H T
  let Q := pCoreOf 2 H
  let ZTK := TKs ⊓ Subgroup.centralizer (TKs : Set (StarQuot M H))
  (kerIn M H = Q → (∃ t ∈ T, cjSub t K ≠ K ∧ M = (M ⊓ K) ⊔ cjSub t (M ⊓ K) ⊔ T) →
    (∀ n : ℕ, 2 ≤ n → (IsPSL 2 2 n ↥Ks ∨ IsSz n ↥Ks) → IsBorelIn Ks MKs →
        E1.nParam H ≤ n) ∧
      (∀ p : ℕ, p.Prime → (p % 8 = 1 ∨ p % 8 = 7) → IsPSL 2 p 1 ↥Ks →
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) → 8 < autCard Ts Ks →
        E1.nParam H = 1)) ∧
  (T ≤ Subgroup.normalizer (K : Set Γ) →
    (∀ x : Γ, x ∈ kerIn M H ↔ x ∈ K ⊔ Q ∧ ∀ y ∈ K ⊔ Q, x * y * x⁻¹ * y⁻¹ ∈ Q) →
    (∀ n : ℕ, IsBenderOf n ↥Ks → IsBorelIn Ks MKs →
        E1.nParam H ≤ n ∧ E1.nParam (⊤ : Subgroup (StarQuot M H)) = n) ∧
      (∀ n : ℕ, 1 ≤ n → (IsPSL 3 2 n ↥Ks ∨ IsSp4Prime n ↥Ks) → IsDiagramNontrivial Ts Ks TKs →
        IsBorelIn Ks MKs → E1.nParam H ≤ n ∧ E1.nParam (⊤ : Subgroup (StarQuot M H)) = n) ∧
      (∀ p e : ℕ, p.Prime → 3 < p → (e = 1 ∨ e = 2) → (p ^ e % 8 = 1 ∨ p ^ e % 8 = 7) →
        IsPSL 2 p e ↥Ks → MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) →
        8 < autCard Ts Ks → E1.nParam H = 1) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 →
        ((p % 4 = 1 ∧ IsPSU 3 p 1 ↥Ks) ∨ (p % 4 = 3 ∧ IsPSL 3 p 1 ↥Ks ∧ InducesOuter Ts Ks)) →
        MKs = Ks ⊓ Subgroup.centralizer (ZTK : Set (StarQuot M H)) → E1.nParam H = 1))

@[expose] def E22NParamC : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M K : Subgroup Γ), MinParabolic H T M → SQTKGroup ↥H →
    ¬ Group.IsSolvable ↥H → K ∈ cComp H → H = K ⊔ T →
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) → E22CasesNoN H T M K →
    SQTKGroup (StarQuot M H) → E22NParamCases H T M K

@[expose] def E22StatementC : Prop :=
  E22StatementNoN ∧ E22NParamC

theorem E22StatementC.toNoN (h : E22StatementC) : E22StatementNoN :=
  h.1

theorem E22StatementC.toNParam (h : E22StatementC) : E22NParamC :=
  h.2

theorem e22CasesNoN_of_e22Cases {H T M K : Subgroup Γ} (h : E22Cases H T M K) :
    E22CasesNoN H T M K := by
  dsimp only [E22Cases] at h
  dsimp only [E22CasesNoN]
  rcases h with ⟨hJ, t, ht, hne, hM, h1⟩ | ⟨hTK, hJ, h2⟩
  · refine Or.inl ⟨hJ, t, ht, hne, hM, ?_⟩
    rcases h1 with ⟨n, hn, hty, hB, -⟩ | ⟨p, hp, hp8, hK, hMK, haut, -⟩
    · exact Or.inl ⟨n, hn, hty, hB⟩
    · exact Or.inr ⟨p, hp, hp8, hK, hMK, haut⟩
  · refine Or.inr ⟨hTK, hJ, ?_⟩
    rcases h2 with ⟨n, hBen, hB, -⟩ | ⟨n, hn, hty, hD, hB, -⟩ |
        ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut, -⟩ | ⟨p, hp, hp2, hK, hMK, -⟩
    · exact Or.inl ⟨n, hBen, hB⟩
    · exact Or.inr (Or.inl ⟨n, hn, hty, hD, hB⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, e, hp, hp3, he, hpe, hK, hMK, haut⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp2, hK, hMK⟩))

theorem e22StatementNoN_of_e22Statement (h : E22Statement) : E22StatementNoN := by
  intro Γ _ _ H T M hmin hSQ hns
  obtain ⟨⟨K, hKc, hHK, hq, hc⟩, hSQs⟩ := h Γ H T M hmin hSQ hns
  exact ⟨⟨K, hKc, hHK, hq, e22CasesNoN_of_e22Cases hc⟩, hSQs⟩

end E2

end CFSG.Quasithin

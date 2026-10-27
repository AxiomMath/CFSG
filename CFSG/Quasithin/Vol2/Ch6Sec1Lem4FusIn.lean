module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4EIn

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def KG614FusionL2 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K T X : Subgroup Γ),
    CFSG.IsQuasisimple (ModO2 K) →
    (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e (ModO2 K)) →
    T ≤ Subgroup.normalizer (K : Set Γ) → IsSylowTwoOf T (K ⊔ T) →
    X ≤ K → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 → ((X ⊓ T).subgroupOf X).Normal →
    T ≤ Subgroup.normalizer (X : Set Γ) →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) →
    ∀ E : Subgroup Γ, E ≤ pCoreOf 2 (X ⊔ T) → IsElemAbelian 2 E → ¬ E ≤ pCoreOf 2 (K ⊔ T) →
      ∃ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ T ∧
        ¬ E.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 (X ⊔ T)

@[expose] def KG614FusionL3 : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K T X : Subgroup Γ),
    CFSG.IsQuasisimple (ModO2 K) →
    (∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧
      IsPSLEps3 δ p 1 (ModO2 K ⧸ Subgroup.center (ModO2 K))) →
    T ≤ Subgroup.normalizer (K : Set Γ) → IsSylowTwoOf T (K ⊔ T) →
    X ≤ K → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 → ((X ⊓ T).subgroupOf X).Normal →
    T ≤ Subgroup.normalizer (X : Set Γ) →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) →
    ∀ E : Subgroup Γ, E ≤ pCoreOf 2 (X ⊔ T) → IsElemAbelian 2 E → ¬ E ≤ pCoreOf 2 (K ⊔ T) →
      ∃ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ T ∧
        ¬ E.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 (X ⊔ T)

theorem kg614Fusion_of (hL2 : KG614FusionL2) (hL3 : KG614FusionL3) : KG614Fusion := by
  intro Γ _ _ K T X hKq hKt
  rcases hKt with h2 | h3
  · exact hL2 Γ K T X hKq h2
  · exact hL3 Γ K T X hKq h3

end CFSG.Quasithin.H13

module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch6Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def KG614Five : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H K T X : Subgroup Γ),
    SQTKGroup ↥H → K ∈ cComp H → CFSG.IsQuasisimple (ModO2 K) →
    T ≤ H → IsPGroup 2 ↥T → T ≤ Subgroup.normalizer (K : Set Γ) → IsSylowTwoOf (T ⊓ K) K →
    X ≤ H → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 → ((X ⊓ T).subgroupOf X).Normal →
    T ≤ Subgroup.normalizer (X : Set Γ) → X ≤ Subgroup.normalizer (K : Set Γ) →
    X ≤ K ⊔ centralizerMod (pCoreOf 2 K) H K → ¬ ⁅X, K⁆ ≤ pCoreOf 2 K →
      X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) ∨
      (X ≤ K ∧ ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e (ModO2 K)) ∨
        ∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧
          IsPSLEps3 δ p 1 (ModO2 K ⧸ Subgroup.center (ModO2 K)))) ∨
      IsTits (ModO2 K)

@[expose] def KG614Fusion : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (K T X : Subgroup Γ),
    CFSG.IsQuasisimple (ModO2 K) →
    ((∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e (ModO2 K)) ∨
      ∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧
        IsPSLEps3 δ p 1 (ModO2 K ⧸ Subgroup.center (ModO2 K))) →
    T ≤ Subgroup.normalizer (K : Set Γ) → IsSylowTwoOf T (K ⊔ T) →
    X ≤ K → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 → ((X ⊓ T).subgroupOf X).Normal →
    T ≤ Subgroup.normalizer (X : Set Γ) →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ K : Subgroup Γ) : Set Γ) →
    ∀ E : Subgroup Γ, E ≤ pCoreOf 2 (X ⊔ T) → IsElemAbelian 2 E → ¬ E ≤ pCoreOf 2 (K ⊔ T) →
      ∃ k ∈ K, E.map (MulAut.conj k).toMonoidHom ≤ T ∧
        ¬ E.map (MulAut.conj k).toMonoidHom ≤ pCoreOf 2 (X ⊔ T)

@[expose] def Res614Tits : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V M₁ K₁ X : Subgroup G),
    Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ → M₁ ≠ M →
    K₁ ∈ cComp M₁ → IsTits (ModO2 K₁) → ¬ K₁ ≤ M →
    X ≤ L → X ≤ M₁ → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
    ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
    X ≤ Subgroup.normalizer (K₁ : Set G) → X ≤ conjClosure K₁ T →
    ¬ X ≤ Subgroup.normalizer ((T ⊓ conjClosure K₁ T : Subgroup G) : Set G) → False

end CFSG.Quasithin.H13

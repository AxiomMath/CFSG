module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def StmtG248 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V V₁ L T H : Subgroup G), AlmostSpecialA5Hyp V V₁ L T H →
    ⁅conjClosure V H, lOne L V₁⁆ ⊔ V₁ = conjClosure V H →
    pCoreOf 2 (lOne L V₁) ≤ pCoreOf 2 H →
    ∀ g ∈ L, g ∉ Subgroup.normalizer (V₁ : Set G) →
      conjClosure V H ⊔ rconj (conjClosure V H) g = L ∧ IsShort2 L ∧ IsAltType L 5 ∧
        pCoreOf 2 L = conjClosure V₁ L ∧ conjClosure V H = pCoreOf 2 (lOne L V₁) ∧
        IsQ8Sq ↥(conjClosure V H)

@[expose] def StmtF956i : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T V L V₁ Vp H : Subgroup G), HypF91 T V L V₁ Vp H →
    Vp.relIndex V = 2 → ¬ V ≤ pCoreOf 2 H →
    (∀ g ∈ H, V₁ < V ⊓ conjSub g⁻¹ V → IsPGroup 2 ↥(V ⊔ conjSub g⁻¹ V)) →
    ⁅V, H ⊓ Subgroup.centralizer (Vp : Set G)⁆ ≤ V₁ → Nat.card V = 2 ^ 4 →
    ∀ h ∈ H, ¬ (∀ x ∈ V ⊔ conjSub h⁻¹ V, ∃ n : ℕ, x ^ 2 ^ n ∈ pCoreOf 2 H) →
      IsQ8Sq ↥(Vp ⊔ conjSub h⁻¹ Vp) ∧
        ∃ _ : ((pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V)).Normal,
          Nonempty (↥(V ⊔ conjSub h⁻¹ V) ⧸ (pCoreOf 2 H).subgroupOf (V ⊔ conjSub h⁻¹ V) ≃*
            Equiv.Perm (Fin 3))

@[expose] def StmtC113c : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T : Subgroup G), IsSylowTwoOf T (L ⊔ T) →
    T ≤ Subgroup.normalizer (L : Set G) → IsShort2 L → IsAltType L 5 →
      pCoreOf 2 (L ⊔ T) = blockU L ⊔ (T ⊓ Subgroup.centralizer (L : Set G)) ∧
        blockU L ⊓ (T ⊓ Subgroup.centralizer (L : Set G)) = ⊥

end CFSG.Quasithin.H13.A5

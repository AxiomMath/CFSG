module

public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped Pointwise

@[expose] def Stmt11_4_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ X : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsCartanX T L X →
      (fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        ∀ v ∈ fsuV T I, ∀ w ∈ fsuV T I, v ≠ 1 → w ≠ 1 → ∃ l ∈ L, l * v * l⁻¹ = w) ∧
      (∀ K : Subgroup G, quasithinIsCComponent K (Subgroup.centralizer (V₁ : Set G)) →
        LOf L V₁ < K → Case11_1_2One K ∨ Case11_1_2Two L K) ∧
      ∀ K : Subgroup G, quasithinIsCComponent K (Subgroup.centralizer (V₁ : Set G)) →
        LOf L V₁ ≤ K → ROf T L V₁ ≤ solvRad (K ⊔ T) ∧ ⁅ROf T L V₁, X⁆ ≤ pCoreOf 2 (K ⊔ T)

@[expose] def Stmt11_4_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ →
      ∀ z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
        KOf L V₁ (Subgroup.zpowers z) = KOf L V₁ V₁

@[expose] def Stmt11_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ →
      ∀ z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
        ((Subgroup.centralizer ({z} : Set G) : Set G) =
            (KOf L V₁ V₁ : Set G) *
              ((Subgroup.centralizer ({z} : Set G) ⊓
                  sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) : Subgroup G) :
                Set G) *
              ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer ({z} : Set G) :
                Subgroup G) : Set G)) ∧
        (KOf L V₁ V₁ = LOf L V₁ →
          ¬ Subgroup.centralizer ({z} : Set G) ⊓
              sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) ≤
            Subgroup.normalizer (L : Set G)) ∧
        (Subgroup.normalizer (V₁ : Set G) : Set G) =
          (KOf L V₁ V₁ : Set G) *
            ((Subgroup.normalizer (V₁ : Set G) ⊓ Subgroup.centralizer (V₁ : Set G) ⊓
                sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) : Subgroup G) :
              Set G) *
            ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
              Set G)

@[expose] def Stmt11_4_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → KOf L V₁ V₁ = LOf L V₁ →
      ∀ z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
        ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
          H ≤ Subgroup.centralizer ({z} : Set G) → E1.nParam H = 1

end CFSG.Quasithin.Vol2.Ch11

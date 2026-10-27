module

public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative Pointwise

@[expose] def VMTwoNatural {G : Type} [Group G] (T L I : Subgroup G) (n : ℕ) : Prop :=
  ∃ W₁ W₂ : Subgroup G, W₁ ≤ VM T L I ∧ W₂ ≤ VM T L I ∧
    L ≤ Subgroup.normalizer (W₁ : Set G) ∧ L ≤ Subgroup.normalizer (W₂ : Set G) ∧
    W₁ ⊓ W₂ = ⊥ ∧ W₁ ⊔ W₂ = VM T L I ∧
    (∃ _ : IsMulCommutative ↥W₁, BinaryNaturalSL (V := ↥W₁) (autOn L W₁) ⊤ ⊥ 3 n) ∧
    (∃ _ : IsMulCommutative ↥W₂, BinaryNaturalSL (V := ↥W₂) (autOn L W₂) ⊤ ⊥ 3 n) ∧
    IsXSectionIso₂ L W₁ ⊥ W₂ ⊥

@[expose] def Stmt11_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ), Hyp11 G T L I n →
    ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
      E1.nParam H ≤ n ∨
      (KindSL3 L (fsuV T I) n ∧ VMTwoNatural T L I n ∧
        fsuV T I ⊓ Subgroup.centralizer (H : Set G) = ⊥ ∧ L = ⁅L, thompsonJ T⁆ ∧
        E1.nParam H ≤ (2 * n : ℕ))

@[expose] def Stmt11_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n m : ℕ) (V₁ V₂ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 2 V₂ →
    (KindG2 L (fsuV T I) n ∧ m = 2 * n ∨ ¬ KindG2 L (fsuV T I) n ∧ m = n) →
      (∀ hV : IsElemAbelian 2 (fsuV T I),
        E3.mParam (autI hV (Subgroup.normalizer (L : Set G))) = m) ∧
      (∀ U : Subgroup G, U ≤ fsuV T I →
        twoPrimeResidual (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (U : Set G)) ≤
          Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G) →
        E3.mQuot (fsuV T I) U < 2 * m →
          Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
          twoPrimeResidual (Subgroup.centralizer (U : Set G)) ≤
            Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (fsuV T I : Set G)) ∧
      ((m : ℕ∞) < E3.rParam (fsuV T I) ∨
        (KindSL3 L (fsuV T I) n ∧ E3.rParam (fsuV T I) = m ∧
          ¬ Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G))) ∧
      (∀ hV : IsElemAbelian 2 (fsuV T I), E3.sParam hV = m) ∧
      (∀ j : ℕ, j + 1 < m → E3.wClos (fsuV T I) j T ≤ TL T L ∧
        V₁ ≤ Subgroup.centralizer (E3.wClos (fsuV T I) j T : Set G)) ∧
      (KindG2 L (fsuV T I) n →
        E3.wClos (fsuV T I) 0 T ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) ∧
        Subgroup.normalizer (E3.wClos (fsuV T I) 0 T : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
        0 < E3.wParam T (fsuV T I)) ∧
      (KindG2 L (fsuV T I) n →
        Subgroup.centralizer (E3.cClos (fsuV T I) 1 (ROf T L V₁) : Set G) ≤
          Subgroup.normalizer (L : Set G))

@[expose] def Stmt11_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ →
      (fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
        (Subgroup.normalizer (V₁ : Set G) : Set G) =
          (Subgroup.centralizer (V₁ : Set G) : Set G) *
            ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) :
              Set G)) ∧
      (Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) →
        Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G))

@[expose] def Stmt11_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 2 V₂ →
    IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G))) →
    ⁅fsuV T I, E3.wClos (fsuV T I) 0 T⁆ ≠ ⊥ →
    (KindSL3 L (fsuV T I) n →
      Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)) →
      E3.wClos (fsuV T I) 0 T ≤ ROf T L V₂ ∧
      (∀ g : G, conjSubgroup (fsuV T I) g ≤ T → ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥ →
        ¬ fsuV T I ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G)) ∧
      E3.rParam (fsuV T I) ≤ (2 * n : ℕ)

@[expose] def Stmt11_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₂ H : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → IsVi T L I n 2 V₂ → InH T H →
    ¬ H ≤ Subgroup.normalizer (L : Set G) →
    (KindSL3 L (fsuV T I) n →
      Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)) →
      ¬ E3.wClos (fsuV T I) 0 T ≤ pCoreOf 2 H ∨
        ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)))

end CFSG.Quasithin.Vol2.Ch11

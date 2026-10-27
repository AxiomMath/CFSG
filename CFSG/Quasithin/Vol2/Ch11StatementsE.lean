module

public import CFSG.Quasithin.Vol2.Ch11StatementsD
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

section Defs

variable {G : Type} [Group G]

structure Hyp11_3_1 (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G) : Prop where
  hstar : IsHStar T (Subgroup.normalizer (L : Set G)) H
  moves : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥
  sl3 : KindSL3 L (fsuV T I) n →
    Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)

@[expose] def Concl11_3_2 (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G) : Prop :=
  KindSp4 L (fsuV T I) n ∧
    ¬ Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G) ∧
    fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
    (E3.wClos (fsuV T I) 0 T ≤ pCoreOf 2 H →
      ¬ IsMulCommutative ↥(conjClosure (fsuV T I) (Subgroup.centralizer (V₁ : Set G))))

@[expose] def Case11_2_1Two (T L I : Subgroup G) (n : ℕ) (H : Subgroup G) : Prop :=
  KindSL3 L (fsuV T I) n ∧ VMTwoNatural T L I n ∧
    fsuV T I ⊓ Subgroup.centralizer (H : Set G) = ⊥ ∧ L = ⁅L, thompsonJ T⁆ ∧
    E1.nParam H ≤ (2 * n : ℕ)

@[expose] def d0Of (D : Subgroup G) : Subgroup G :=
  opResidual 3 D ⊔ Subgroup.closure {x | x ∈ pCoreOf 3 D ∧ x ^ 3 = 1}

end Defs

@[expose] def Stmt11_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → Hyp11_3_1 T L I n V₁ H → Concl11_3_2 T L I n V₁ H

@[expose] def Stmt11_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → Hyp11_3_1 T L I n V₁ H →
    ¬ Concl11_3_2 T L I n V₁ H → ¬ E3.wClos (fsuV T I) 0 T ≤ pCoreOf 2 H

@[expose] def Stmt11_3_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G) (g : G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → Hyp11_3_1 T L I n V₁ H →
    ¬ Concl11_3_2 T L I n V₁ H → conjSubgroup (fsuV T I) g ≤ T →
    ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G) →
      (∃ _ : IsMulCommutative ↥(VZ T H), ∀ hV : IsElemAbelian 2 (fsuV T I),
        autOn (conjSubgroup (fsuV T I) g) (VZ T H) ∈
          E3.aSet (E3.sParam hV) (autOn H (VZ T H))) ∧
      (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) ∧
      (E1.nParam H = n ∨ ((n : ℕ∞) < E1.nParam H ∧ Case11_2_1Two T L I n H)) ∧
      Subgroup.normalizer (V₁ : Set G) ≤
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (fsuV T I : Set G)

@[expose] def Stmt11_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → Hyp11_3_1 T L I n V₁ H →
    ¬ Concl11_3_2 T L I n V₁ H →
      ∃ k : ℕ, E1.nParam H = k ∧ ∃ K : Subgroup G, quasithinIsCComponent K H ∧
        oTwoUpper H = conjClosure K H ∧
        (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ k ∧
          Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∧
        ((n < k → k = 2 * n) → K = oTwoUpper H)

@[expose] def Stmt11_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ H : Subgroup G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → Hyp11_3_1 T L I n V₁ H →
    ¬ Concl11_3_2 T L I n V₁ H → E1.nParam H = n

@[expose] def Stmt11_3_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ H D : Subgroup G) (g : G),
    Hyp11 G T L I n → IsVi T L I n 1 V₁ → Hyp11_3_1 T L I n V₁ H →
    ¬ Concl11_3_2 T L I n V₁ H → conjSubgroup (fsuV T I) g ≤ T →
    ¬ conjSubgroup (fsuV T I) g ≤ Subgroup.centralizer (VZ T H : Set G) →
    QuasithinUnique.Lin2.IsHallTwoPrimeOf D (H ⊓ Subgroup.normalizer (L : Set G)) →
      (quasithinIsCComponent (oTwoUpper H) H ∧
        Nonempty (↥(autOn (oTwoUpper H) (VZ T H)) ≃*
          ↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃*
            Matrix.SpecialLinearGroup (Fin 2) F)) ∧
      d0Of D ≤ L ∧
      (quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
        VZ T H ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥) ∧
      (fsuV T I = conjSubgroup (fsuV T I) g ∧
        QuasithinUnique.IsSylowTwoOf (autOn (fsuV T I) (VZ T H))
          (autOn (oTwoUpper H) (VZ T H))) ∧
      V₁ = ⁅V₁, d0Of D⁆ ∧ ∃ X : Subgroup G, IsCartanX T L X ∧ d0Of D ≤ X

end CFSG.Quasithin.Vol2.Ch11

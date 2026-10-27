module

public import CFSG.Quasithin.Vol2.Ch10StatementsA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs
public import CFSG.Quasithin.Background.A3Structure316
public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative MatrixGroups

abbrev LBarL32 {G : Type} [Group G] (L : Subgroup G) : Prop :=
  Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))

abbrev SymFiveWrTwo : Type :=
  RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))

@[expose] def Stmt10_1_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    fsuVM T L I ≤ fsuM T L ∧ IsPrimeReduced 2 ((fsuVM T L I).subgroupOf (fsuM T L)) ∧
    (∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) →
      fsuVM T L I = ⁅fsuVM T L I, L⁆ ⊔ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ∧
      ⁅fsuVM T L I, L⁆ ≤ Subgroup.centralizer (CFSG.conjugate L t : Set G) ∧
      ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ Subgroup.centralizer (L : Set G) ∧
      (⁅fsuVM T L I, L⁆ ⊔ fsuCVM T L I) ⊓ (⁅fsuVM T L I, CFSG.conjugate L t⁆ ⊔ fsuCVM T L I) =
        fsuCVM T L I) ∧
    Cases10_1_1 T L I

@[expose] def Stmt10_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    (¬ ((∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I ∨ Case10_1_1Three T L I) →
      (∀ _ : IsMulCommutative ↥(fsuVM T L I),
        ¬ IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I))) ∧
      thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G)) ∧
    thompsonJ T ≤ T1 T L ∧
    (¬ Case10_1_1Six T L I →
      T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) = pCoreOf 2 (fsuL0 T L ⊔ T)) ∧
    (Case10_1_1Six T L I → fsuL0 T L ⊔ T ≤
      Subgroup.normalizer ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G)) ∧
    IsUniqueM (Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G)) (fsuM T L) ∧
    IsUniqueM (Subgroup.normalizer
      (thompsonJ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) : Set G)) (fsuM T L) ∧
    (¬ ((∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Three T L I) → fsuCVM T L I = ⊥) ∧
    (¬ LBarL32 L → ∀ D : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf D (B0 T L) →
      ((∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Seven T L I →
        D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = ⊥) ∧
      ∀ n : ℕ, Case10_1_1Four T L I n →
        ∃ f : ↥(D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →*
          Multiplicative (ZMod (2 ^ n + 1) × ZMod (2 ^ n + 1)), Function.Injective f) ∧
    ((∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I →
      MinParabolic (fsuL0 T L ⊔ T) T
          ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (T0 T L : Set G)) ∧
        (¬ thompsonJ T ≤ Subgroup.centralizer (fsuVM T L I : Set G) → baum T ≤ T1 T L))

@[expose] def Stmt10_1_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) →
      oPrimeResidualOf p (fsuM T L) = fsuL0 T L

@[expose] def Stmt10_2_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ¬ Case10_1_1Three T L I → Subgroup.normalizer (baum T : Set G) ≤ fsuM T L

@[expose] def Stmt10_2_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ →
      (fsuL0 T L = ⁅fsuL0 T L, thompsonJ T⁆ ∧
        ((∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I ∨ Case10_1_1Three T L I)) ∧
      ((∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I →
        (oTwoUpper H = ⁅oTwoUpper H, thompsonJ T⁆ ∧
          ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) ∧
          ∃ _ : IsMulCommutative ↥(VZ T H), IsFFModule (V := ↥(VZ T H)) (autOn H (VZ T H))) ∧
        ((∃ n, Case10_1_1One T L I n) →
          B0 T L ≤ Subgroup.normalizer (baum T : Set G) ∧
            QuasithinUnique.IsSylowTwoOf (baum T) (fsuL0 T L ⊔ baum T)) ∧
        pCoreOf 2 (Subgroup.normalizer (baum T : Set G) ⊔ H) ≠ ⊥)

@[expose] def Stmt10_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    ∀ H : Subgroup G, IsHStar T (fsuM T L) H → 1 < E1.nParam H →
      E1.nParam H = 2 ∧
      (∀ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) →
        ∀ b ∈ B, (∀ l ∈ fsuL0 T L,
          b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuVM T L I : Set G)) → b = 1) ∧
      (LBarL32 L →
        oTwoUpper (H ⊓ fsuM T L) ≤ fsuL0 T L ∧
        (∀ K : Subgroup G, IsLi T L K →
          IsMaxSubgroupIn K ((T0 T L ⊔ oTwoUpper (H ⊓ fsuM T L)) ⊓ K)) ∧
        Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* SymFiveWrTwo)) ∧
      ¬ ∃ n, Case10_1_1One T L I n

section Notation

variable {G : Type} [Group G]

abbrev KOf (P H : Subgroup G) : Subgroup G :=
  conjClosure (oTwoUpper P) H

end Notation

@[expose] def Stmt10_2_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I → LBarL32 L →
    ¬ Case10_1_1Five T L I →
    ∀ P : Subgroup G, IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P →
    ∀ H : Subgroup G, InH (oTwoUpper P ⊔ T) H →
      KOf P H = oTwoUpper P ∨
      (∃ K₁ : Subgroup G, ∃ s ∈ T, quasithinIsCComponent K₁ H ∧
        s ∉ Subgroup.normalizer (K₁ : Set G) ∧ KOf P H = K₁ ⊔ CFSG.conjugate K₁ s ∧
        ((∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ m ∧
            Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
          ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p)))) ∨
      (quasithinIsCComponent (KOf P H) H ∧ ∃ k : ℕ, (k = 4 ∨ k = 5) ∧
        Nonempty (↥(KOf P H ⊔ T) ⧸ CFSG.pCore 2 ↥(KOf P H ⊔ T) ≃*
          MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))))

end CFSG.Quasithin.Vol2.Ch10

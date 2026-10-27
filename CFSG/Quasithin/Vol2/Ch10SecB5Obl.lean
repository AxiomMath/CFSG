module

public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin CFSG.QuasithinUnique
open scoped MatrixGroups

@[expose] def Gap10_2_5L2p : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I →
    ∀ P : Subgroup G, IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P →
    ∀ (K₁ : Subgroup G) (s : G), s ∈ T →
      K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ P) →
      s ∉ Subgroup.normalizer (K₁ : Set G) →
      conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P) =
        K₁ ⊔ CFSG.conjugate K₁ s →
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p))) →
      Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (oTwoUpper P : Set G)

@[expose] def Obl10_2_5Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I →
    ∀ P : Subgroup G, IsMaxSubgroupIn (fsuL0 T L ⊔ T) P → T ≤ P →
      ((∃ (K₁ : Subgroup G) (s : G), s ∈ T ∧
          K₁ ∈ cComp (Subgroup.normalizer (T1 T L : Set G) ⊔ P) ∧
          s ∉ Subgroup.normalizer (K₁ : Set G) ∧
          conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P) =
            K₁ ⊔ CFSG.conjugate K₁ s ∧
          ∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
            Nat.card F = 2 ^ m ∧
            Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        (quasithinIsCComponent
            (conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P))
            (Subgroup.normalizer (T1 T L : Set G) ⊔ P) ∧
          ∃ k : ℕ, (k = 4 ∨ k = 5) ∧
            CFSG.Assembly.LowTwoRank.StatedClassicalModel
              (↥(conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P)) ⧸
                CFSG.pCore 2
                  ↥(conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P)))
              .PSL k 2 1 ∧
            Nonempty
              (↥(conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P) ⊔ T) ⧸
                  CFSG.pCore 2
                    ↥(conjClosure (oTwoUpper P) (Subgroup.normalizer (T1 T L : Set G) ⊔ P) ⊔ T) ≃*
                MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))))) →
      Subgroup.normalizer (T1 T L : Set G) ≤ Subgroup.normalizer (oTwoUpper P : Set G)

end CFSG.Quasithin.Vol2.Ch10.SecB

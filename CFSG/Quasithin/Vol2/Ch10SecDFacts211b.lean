module

public import CFSG.Quasithin.Vol2.Ch10StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups

@[expose] def FactVEIrred : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → fsuCVM T L I = ⊥ → ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      ∀ U : Subgroup G, Subgroup.closure {v₁, v₂} ≤ U → U ≤ fsuVM T L I →
        Xz T L (v₁ * v₂) ≤ Subgroup.normalizer (U : Set G) →
        T ≤ Subgroup.normalizer (U : Set G) →
          U = Subgroup.closure {v₁, v₂} ∨ U = fsuVM T L I

@[expose] def FactVXE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → fsuCVM T L I = ⊥ → ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      fsuVM T L I = ⁅fsuVM T L I, Xz T L (v₁ * v₂)⁆ ⊔ Subgroup.closure {v₁, v₂}

@[expose] def FactMaxP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → fsuCVM T L I = ⊥ → ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      IsMaxSubgroupIn (fsuL0 T L ⊔ T)
        ((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G))

@[expose] def Concl10_2_4TwoThree {G : Type} [Group G] (T K H : Subgroup G) : Prop :=
  (∃ K₁ : Subgroup G, ∃ s ∈ T, quasithinIsCComponent K₁ H ∧
      s ∉ Subgroup.normalizer (K₁ : Set G) ∧ K = K₁ ⊔ CFSG.conjugate K₁ s ∧
      ((∃ m : ℕ, 0 < m ∧ Even m ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
          Nat.card F = 2 ^ m ∧
          Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* PSL(2, ZMod p)))) ∨
    (quasithinIsCComponent K H ∧ ∃ k : ℕ, (k = 4 ∨ k = 5) ∧
      Nonempty (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T) ≃*
        MulAut (Matrix.SpecialLinearGroup (Fin k) (ZMod 2))))

@[expose] def FactTransvList : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp10 G T L I →
    Case10_1_1Three T L I → fsuCVM T L I = ⊥ → ∀ t v₁ v₂ : G, IsData10_2_11 T L I t v₁ v₂ →
      Xz T L (v₁ * v₂) < Kz T L (v₁ * v₂) →
      IsPrimeReduced 2 ((Vz v₁ v₂).subgroupOf (Subgroup.centralizer ({v₁ * v₂} : Set G))) →
      fsuVM T L I ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) = Subgroup.closure {v₁, v₂} →
      Concl10_2_4TwoThree T (Kz T L (v₁ * v₂)) (Subgroup.centralizer ({v₁ * v₂} : Set G)) →
        v₁ * v₂ ∈ ⁅Vz v₁ v₂, Kz T L (v₁ * v₂)⁆ ∧
          ⁅Vz v₁ v₂, Kz T L (v₁ * v₂)⁆ ⊓ Subgroup.centralizer (Kz T L (v₁ * v₂) : Set G) = ⊥

end CFSG.Quasithin.Vol2.Ch10.SecD

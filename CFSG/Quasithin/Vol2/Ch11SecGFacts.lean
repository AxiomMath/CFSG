module

public import CFSG.Quasithin.Vol2.Ch11SecDFacts

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

@[expose] def CommEndStableFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ : Subgroup G),
    SecD.NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → ∀ X : Subgroup G, X ≤ ROf T L V₁ →
      IsEndStable L (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) ⁅fsuV T I, X⁆

@[expose] def R1CommFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → IsVi T L I n 3 V₃ → ∀ A : Subgroup G, A ≤ ROf T L V₁ →
      ⁅fsuV T I, A⁆ ≠ ⊥ → ⁅fsuV T I, A⁆ = V₁ ∨ ⁅V₃, A⁆ = V₁

@[expose] def PointConjFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ P : Subgroup G),
    SecD.NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → P ≤ fsuV T I →
    IsEndStable L (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) P →
    Nat.card P = 2 ^ n → ∃ l ∈ L, P = conjSubgroup V₁ l

@[expose] def R1CorankFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ) (V₁ V₃ : Subgroup G),
    SecD.NatSetting11 G T L I n → (KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) →
    IsVi T L I n 1 V₁ → IsVi T L I n 3 V₃ → ∀ D B : Subgroup G, D ≤ ROf T L V₁ → B ≤ V₃ →
      E3.mQuot V₃ B ≤ 1 → D ≤ Subgroup.centralizer (B : Set G) → ⁅fsuV T I, D⁆ ≤ V₁

@[expose] def FactTransv11_5_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H K T L₁ Y A : Subgroup G),
    CFSG.SectionRank.IsSQTKCat ↥H →
    K ≤ H → H ≤ Subgroup.normalizer (K : Set G) → QuasithinUnique.IsSylowTwoOf T H →
    K ⊔ T = H → ⁅K, K⁆ = K →
    (List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) 2 ∨ List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K)) →
    (Case11_1_2One K ∨ ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ IsPSL 2 p 1 (↥K ⧸ CFSG.pCore 2 ↥K)) →
    L₁ ≤ K → ⁅L₁, L₁⁆ = L₁ →
    (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F)) →
    conjClosure L₁ K = K →
    Y ≤ H → H ≤ Subgroup.normalizer (Y : Set G) → IsElemAbelian 2 Y →
    K ⊓ Subgroup.centralizer (Y : Set G) ≤ Subgroup.normalizer (L₁ : Set G) →
    A ≤ H → IsPGroup 2 A → ¬ A ≤ pCoreOf 2 H →
    E3.mQuot Y (Y ⊓ Subgroup.centralizer (A : Set G)) ≤ 1 → False

end CFSG.Quasithin.Vol2.Ch11.SecG

module

public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSp)

@[expose] def A312LeviField : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (B L : Subgroup X), A312C2 B L →
    ∃ f n : ℕ, f ∣ n ∧ IsPSL 2 2 n (ModO2 B) ∧
      ((1 ≤ f ∧ IsPSL 3 2 f ↥L) ∨ (1 ≤ f ∧ IsSL3 (2 ^ f) ↥L) ∨ (2 ≤ f ∧ IsPSp4 2 f ↥L) ∨
        (2 ≤ f ∧ IsG2 2 f ↥L) ∨ (1 ≤ f ∧ Is3D4 2 f ↥L) ∨ (Odd f ∧ 3 ≤ f ∧ Is2F4 f ↥L))

@[expose] def A312AutCent : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X → IsSQTKCat X → CFSG.pCore 2 X = ⊥ →
    ∀ T : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf T ⊤ → ∀ B ∈ lFamily T, B ≠ ⊤ →
      T ≤ Subgroup.normalizer (B : Set X) →
      ((∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
        Nonempty (ModO2 B ≃* alternatingGroup (Fin 5)) ∨
        Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
        ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (ModO2 B) 2 n) →
      ∀ V : Subgroup X, V ≤ B → IsElemAbelian 2 V → B ≤ Subgroup.normalizer (V : Set X) →
        ⁅V, B⁆ = V → V ≠ ⊥ → pCoreOf 2 B ≤ Subgroup.centralizer (V : Set X) →
        (∃ (I : Type) (_ : Group I) (_ : Finite I) (π : I →* X), Function.Surjective π ∧
          π.ker ≤ Subgroup.center I ∧ IsPGroup 2 π.ker ∧
          ⁅(⊤ : Subgroup I), (⊤ : Subgroup I)⁆ = ⊤ ∧
          ∃ V₁ : Subgroup I, V₁.map π = V ∧
            Subgroup.normalizer (V₁ : Set I) ≤
              Subgroup.normalizer ((B.comap π : Subgroup I) : Set I)) →
      (∀ α : MulAut X, (∀ b ∈ B, α b = b) → (∀ t ∈ T, α t ∈ T) → (∃ k : ℕ, α ^ 2 ^ k = 1) →
          α = 1) ∨
        ∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
          Nonempty (X ⧸ Subgroup.center X ≃* ↥(StatedSp 2 F)) ∧
          Nonempty (ModO2 B ≃* Matrix.SpecialLinearGroup (Fin 2) F)

end CFSG.Quasithin.Vol2.Ch10

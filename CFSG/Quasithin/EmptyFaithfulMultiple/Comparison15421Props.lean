module

public import CFSG.Quasithin.Background.F6Cat
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.EmptyFaithfulMultiple.FFLinearModel

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open (quasithinG2)
open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def F618ComponentInspection : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtTriple G₁ G₂ →
    (∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X)) →
    F6.F618ConclusionCat G₁ G₂ → ∀ M : Subgroup D, CFSG.IsComponent M →
      (∀ (K : Type) [Field K] [Finite K] [CharP K 2], ¬ Nonempty (↥M ≃* ↥(StatedSL 2 K))) ∧
      Odd (Nat.card ↥(Subgroup.centralizer (M : Set D))) ∧
      (Nonempty (↥M ≃* ↥(alternatingGroup (Fin 6))) → Subgroup.centralizer (M : Set D) = ⊥)

@[expose] def FixG2Derived : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∃ T₀ : Subgroup ↥⁅quasithinG2 K, quasithinG2 K⁆, IsPGroup 2 ↥T₀ ∧
      ∃ γ : ↥⁅quasithinG2 K, quasithinG2 K⁆, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
        FFL.FixesFixed (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆) T₀ γ

@[expose] def FixA7Four : Prop :=
  ∀ α : ↥(alternatingGroup (Fin 8)) ≃* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2),
    ∃ T₀ : Subgroup ↥(alternatingGroup (Fin 7)), IsPGroup 2 ↥T₀ ∧
      ∃ γ : ↥(alternatingGroup (Fin 7)), γ ^ 3 = 1 ∧ γ ≠ 1 ∧
        FFL.FixesFixed (FFModel.a7Four α) T₀ γ

@[expose] def FixTripleA6 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
    ∀ Γ₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K),
      (∀ g ∈ Γ₀, ((g : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1) →
      IsHat ↥Γ₀ ↥(alternatingGroup (Fin 6)) →
      (∀ g ∈ Subgroup.center ↥Γ₀, ∃ c : K,
        (((g : ↥Γ₀) : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) →
      ∃ T₀ : Subgroup ↥Γ₀, IsPGroup 2 ↥T₀ ∧ ∃ γ : ↥Γ₀, γ ^ 3 = 1 ∧ γ ≠ 1 ∧
        FFL.FixesFixed (FFModel.nat Γ₀) T₀ γ

end CFSG.Quasithin.EmptyFaithfulMultiple

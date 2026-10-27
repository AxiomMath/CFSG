module

public import CFSG.Quasithin.MS93.ML3Bridge

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Matrix

variable {F : Type} [Field F]

@[expose] def ptStab : Subgroup (SL3 F) where
  carrier := {g | ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0}
  mul_mem' := fun {g h} hg hh => by
    change ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) * ((h : SL3 F) : Matrix _ _ F) ∈
      {A : Matrix (Fin 3) (Fin 3) F | A 1 0 = 0 ∧ A 2 0 = 0}
    simp only [Set.mem_ofPred_eq, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2, hh.1, hh.2]
    simp
  one_mem' := by
    change ((1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ _
    simp
  inv_mem' := fun {g} hg => by
    change ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧
      ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
    simp [hg.1, hg.2]

@[expose] def ptLevi : Subgroup (SL3 F) :=
  rootGroup 0 1 ⊔ rootGroup 0 2 ⊔ rootGroup 1 2 ⊔ rootGroup 2 1

section Internal

variable {𝔾 : Type*} [Group 𝔾] {L : Subgroup 𝔾}

@[expose] noncomputable def qPtPre (L : Subgroup 𝔾)
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : Subgroup 𝔾 :=
  ((qPt : Subgroup (SL3 F)).comap (toSL3 α)).map L.subtype

end Internal

@[expose] def MS17i : Prop :=
  ∀ (𝔾 : Type) [Group 𝔾] (F : Type) [Field F] [Fintype F] (n : ℕ), Fintype.card F = 2 ^ n →
  ∀ (L Z W U C X : Subgroup 𝔾) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
    Function.Surjective α →
    IsSumOfNaturalModulesVia L Z ⊥ α false 1 →
    IsSumOfNaturalModulesVia L U C α false 1 →
    Z ≤ C → ⁅C, L⁆ ≤ Z →
    L ≤ Subgroup.normalizer (W : Set 𝔾) →
    ⁅Z, U⁆ = ⊥ → ⁅Z, W⁆ = ⊥ → ⁅U, W⁆ ≤ Z →
    X ≤ U → U = Subgroup.closure {u | ∃ l : ↥L, ∃ x ∈ X, (l : 𝔾) * x * (l : 𝔾)⁻¹ = u} →
    (∀ l : ↥L, toSL3 α l ∈ ptStab → ∀ x ∈ X, (l : 𝔾) * x * (l : 𝔾)⁻¹ ∈ X) →
    (∀ l : ↥L, toSL3 α l ∈ ptLevi → ∀ x ∈ X, x⁻¹ * ((l : 𝔾) * x * (l : 𝔾)⁻¹) ∈ C) →
    ⁅X, W⁆ ≠ ⊥ → Nat.card ↥⁅X, W⁆ ≤ Nat.card F ^ 2 →
    ⁅C, W⁆ = ⊥ ∧ ⁅⁅W, L⁆, U⁆ = ⊥ ∧ U ⊓ Subgroup.centralizer (W : Set 𝔾) = C ∧
      W ⊓ Subgroup.centralizer (X : Set 𝔾) = W ⊓ Subgroup.centralizer (U : Set 𝔾) ∧
      ∀ w ∈ W, w ∉ Subgroup.centralizer (U : Set 𝔾) → ⁅U, Subgroup.zpowers w⁆ = Z

@[expose] def wOff {V : Type*} [CommGroup V] (ρ : SL3 F →* MulAut V) (W₀ : Subgroup V) :
    Subgroup V :=
  ⨆ (g : SL3 F) (_ : (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 2 ≠ 0),
    W₀.map (ρ g).toMonoidHom

end CFSG.Quasithin.MS93

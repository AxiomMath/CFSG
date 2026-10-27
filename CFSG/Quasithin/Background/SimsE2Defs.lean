module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Background.A4Defs

open scoped Pointwise commutatorElement

public section

namespace CFSG.Quasithin.SimsE2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def IsSp4Full (n : ℕ) (X : Type) [Group X] : Prop :=
  IsPSp4 2 n X ∨ (n = 1 ∧ Nonempty (X ≃* Equiv.Perm (Fin 6)))

@[expose] def rootGroupOfParabolic {Y : Type*} [Group Y] (P : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {x : Y | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} ⊓
    Subgroup.centralizer
      (Subgroup.closure {x : Y | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} : Set Y)

@[expose] def IsInIHTV {Γ : Type} [Group Γ] (H T M V I : Subgroup Γ) : Prop :=
  I ≤ H ∧ (∃ g ∈ I, I = V ⊔ conjSubgroup V g) ∧ IsSylowTwoOf (T ⊓ I) I ∧
    IsSylowTwoOf (pCoreOf 2 (kerIn (M ⊓ I) I)) (kerIn (M ⊓ I) I) ∧
    ∃ k : ℕ, (∃ m : ℕ, E1.nParam (⊤ : Subgroup (E2.StarQuot M H)) = ((k * m : ℕ) : ℕ∞)) ∧
      ((1 < k ∧ (IsPSL 2 2 k (E2.StarQuot (M ⊓ I) I) ∨ IsSz k (E2.StarQuot (M ⊓ I) I)) ∧
          E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I))) ∨
        (k = 1 ∧ ∃ p a : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ a ∧
          Nonempty (E2.StarQuot (M ⊓ I) I ≃* DihedralGroup (p ^ a))) ∨
        ((∃ n : ℕ, E2.IsSp4Prime n ↥(oTwoUpper (⊤ : Subgroup (E2.StarQuot M H)))) ∧ 1 ≤ k ∧
          IsSp4Full k (E2.StarQuot (M ⊓ I) I) ∧
          E2.IsBorelIn ⊤ (E2.star (M ⊓ I) I (M ⊓ I)) ∧
          E2.star (M ⊓ I) I V ≤
            Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) ∧
          ∀ P : Subgroup (E2.StarQuot (M ⊓ I) I), IsMaxParabolic2 ⊤ P →
            E2.star (M ⊓ I) I (M ⊓ I) ≤ P → ¬ E2.star (M ⊓ I) I V ≤ rootGroupOfParabolic P))

@[expose] def IsL33Exception {Y : Type} [Group Y] (H V : Subgroup Y) : Prop :=
  IsPSL 3 3 1 ↥(oTwoUpper H) ∧ ¬ V ≤ oTwoUpper H

@[expose] def IsNaturalSection {Γ : Type} [Group Γ] {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] (I U Z J : Subgroup Γ) (S : Subgroup (Matrix.GeneralLinearGroup ι F)) :
    Prop :=
  Z ≤ U ∧ J ≤ I ∧ I ≤ Subgroup.normalizer (U : Set Γ) ∧
    I ≤ Subgroup.normalizer (Z : Set Γ) ∧
  ∃ (ρ : ↥I →* ↥S) (ψ : ↥U →* Multiplicative (ι → F)),
    Function.Surjective ρ ∧ ρ.ker = J.subgroupOf I ∧ Function.Surjective ψ ∧
    ψ.ker = Z.subgroupOf U ∧
    ∀ (i : ↥I) (u v : ↥U), (v : Γ) = (i : Γ) * (u : Γ) * (i : Γ)⁻¹ →
      ψ v = Multiplicative.ofAdd
        ((((ρ i : ↥S) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F).mulVec
          (Multiplicative.toAdd (ψ u)))

@[expose] def IsSumOfNaturalSections {Γ : Type} [Group Γ] {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] (r : ℕ) (I P Z J : Subgroup Γ)
    (S : Subgroup (Matrix.GeneralLinearGroup ι F)) : Prop :=
  ∃ W : Fin r → Subgroup Γ, (∀ i, Z ≤ W i ∧ W i ≤ P ∧ I ≤ Subgroup.normalizer (W i : Set Γ) ∧
      IsNaturalSection I (W i) Z J S) ∧
    (⨆ i, W i) = P ∧ ∀ i, W i ⊓ (⨆ j, ⨆ (_ : j ≠ i), W j) ≤ Z

@[expose] def IsFaithfulIrredSection {Γ : Type} [Group Γ] (I U Z J : Subgroup Γ) : Prop :=
  Z < U ∧ I ≤ Subgroup.normalizer (U : Set Γ) ∧ I ≤ Subgroup.normalizer (Z : Set Γ) ∧
    (∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ Z) ∧ (∀ x ∈ U, x ^ 2 ∈ Z) ∧
    (∀ Y : Subgroup Γ, Z ≤ Y → Y ≤ U → I ≤ Subgroup.normalizer (Y : Set Γ) → Y = Z ∨ Y = U) ∧
    ∀ x : Γ, x ∈ J ↔ x ∈ I ∧ ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ Z

@[expose] def E27Stmt : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (H T M V : Subgroup Γ), MinParabolic H T M → SQTKGroup ↥H →
    kerIn M H = ⊥ → V ≠ ⊥ → IsElemAbelian 2 V → V ≤ T → T ≤ Subgroup.normalizer (V : Set Γ) →
    V ≤ pCoreOf 2 M → ¬ IsL33Exception H V → ∃ I : Subgroup Γ, IsInIHTV H T M V I

end CFSG.Quasithin.SimsE2

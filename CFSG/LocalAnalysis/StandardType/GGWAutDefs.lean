module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112K
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGWeylModel3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (C : Matrix (Fin n) (Fin n) ℤ) (A : Subgroup (V ≃ₗ[ZMod 3] V)) : Prop :=
  ∃ (z : Fin n → V) (α : Fin n → Module.Dual (ZMod 3) V),
    LinearIndependent (ZMod 3) z ∧ Submodule.span (ZMod 3) (Set.range z) = ⊤ ∧
      (∀ i j, α i (z j) = ((C i j : ℤ) : ZMod 3)) ∧ A = ggQ2WeylOf z α

@[expose] def GGOrthType {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (R : Subgroup (V ≃ₗ[ZMod p] V)) : Prop :=
  ∃ Q : QuadraticForm (ZMod p) V, (QuadraticMap.polarBilin Q).Nondegenerate ∧
    (∀ g ∈ R, ZS.IsIsom p Q g) ∧
    ∀ g h : V ≃ₗ[ZMod p] V, ZS.IsIsom p Q g → ZS.IsIsom p Q h → g * h * g⁻¹ * h⁻¹ ∈ R

@[expose] def GGReflClassOmegaLarge : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V]
    [Module.Finite (ZMod p) V] (n : ℕ), Module.finrank (ZMod p) V = n → 9 ≤ n →
    ∀ A : Subgroup (V ≃ₗ[ZMod p] V), ZS.AbsIrred p A →
      A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} →
      CFSG.Quasithin.SimsG4.IsImprimitiveOnV A ∨
        ((∀ g : V ≃ₗ[ZMod p] V, LinearEquiv.det g = 1 → g ∈ A) ∧
          p ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A) ∨
        (GGOrthType A ∧ p ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A) ∨
        (¬ p ∣ n + 1 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod p] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
        (p ∣ n + 2 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod p] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)

@[expose] def GGReflClassOmegaSmall : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] (n : ℕ),
    Module.finrank (ZMod 3) V = n → 5 ≤ n → n ≤ 8 →
    ∀ A : Subgroup (V ≃ₗ[ZMod 3] V), ZS.AbsIrred 3 A →
      A = Subgroup.closure {r | r ∈ A ∧ GGLinRefl r} →
      CFSG.Quasithin.SimsG4.IsImprimitiveOnV A ∨
        ((∀ g : V ≃ₗ[ZMod 3] V, LinearEquiv.det g = 1 → g ∈ A) ∧
          3 ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A) ∨
        (GGOrthType A ∧ 3 ^ (n * (n - 1) / 2) ≤ 8 * Nat.card A) ∨
        (¬ 3 ∣ n + 1 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 1)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
        (3 ∣ n + 2 ∧ ∃ e : A ≃* Equiv.Perm (Fin (n + 2)),
          ∀ r : A, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j) ∨
        (n = 7 ∧ GGWeylModel3 (CartanMatrix.E 7) A) ∨ (n = 8 ∧ GGWeylModel3 (CartanMatrix.E 8) A)

@[expose] def GGReflClassOmegaInput : Prop := GGReflClassOmegaLarge ∧ GGReflClassOmegaSmall

theorem ggReflClassLargeInput_of_omega (h : GGReflClassOmegaLarge) : GGReflClassLargeInput' := by
  intro p _ hp V _ _ _ n hn h9 A habs hgen
  rcases h p hp V n hn h9 A habs hgen with h1 | ⟨-, h2⟩ | ⟨-, h3⟩ | h4 | h5
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h4))
  · exact Or.inr (Or.inr (Or.inr h5))

@[expose] def GGWAutEngine : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V] (n : ℕ),
    Module.finrank (ZMod 3) V = n → 5 ≤ n →
    ∀ A : Subgroup (V ≃ₗ[ZMod 3] V), TransvectionFree A → ZS.AbsIrred 3 (reflGp A) →
      (Even n ∧ GGOrthType (reflGp A)) ∨
        ∀ a ∈ A, ∃ r ∈ reflGp A, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v))

section Defs2

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Module.Finite (ZMod 3) V]

@[expose] def GGMonomialIn {n : ℕ} (f : Fin n → V) (g : V ≃ₗ[ZMod 3] V) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i ≠ 0) ∧ ∀ i, g (f i) = ε i • f (σ i)

@[expose] def GGMonomialEvenIn {n : ℕ} (f : Fin n → V) (g : V ≃ₗ[ZMod 3] V) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3), (∀ i, ε i ≠ 0) ∧ (∏ i, ε i = 1) ∧
    ∀ i, g (f i) = ε i • f (σ i)

@[expose] def ggOmega (Q : QuadraticForm (ZMod 3) V) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  Subgroup.closure {c | ∃ g h : V ≃ₗ[ZMod 3] V, ZS.IsIsom 3 Q g ∧ ZS.IsIsom 3 Q h ∧
    c = g * h * g⁻¹ * h⁻¹}

end Defs2

end CFSG.StandardType

end

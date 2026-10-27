module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Comp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Endgame

variable {X : Type} [Group X]

@[expose] def EgenX (A : Subgroup X) : Subgroup X :=
  ⨆ (g : X) (_ : ∀ z ∈ A, ∀ y ∈ conjSubgroup g A, z * y = y * z), conjSubgroup g A

@[expose] def IsTIOf (A : Subgroup X) : Prop :=
  ∀ g : X, ∀ u ∈ A, u ≠ 1 → g * u * g⁻¹ ∈ A → g ∈ Subgroup.normalizer (A : Set X)

@[expose] def CommAllOf (A : Subgroup X) : Prop :=
  ∀ g h : X, ∀ x ∈ conjSubgroup g A, x ≠ 1 → ∀ y ∈ conjSubgroup h A, y ≠ 1 → x * y = y * x →
    ∀ x' ∈ conjSubgroup g A, ∀ y' ∈ conjSubgroup h A, x' * y' = y' * x'

@[expose] def CentOneOf (H A : Subgroup X) : Prop :=
  ∀ h ∈ H, ∀ a ∈ A, a ≠ 1 → h * a = a * h → ∀ b ∈ A, h * b = b * h

@[expose] def InOmegaA (A : Subgroup X) (g : X) : Prop :=
  ∀ z ∈ A, ∀ y ∈ conjSubgroup g A, z * y = y * z

structure EndOmegaHyp (A : Subgroup X) : Prop where
  ne_bot : A ≠ ⊥
  sq : ∀ a ∈ A, a * a = 1
  comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  ti : IsTIOf A
  n1 : CommAllOf A
  e : ⁅EgenX A, EgenX A⁆ ≤ A

structure OmegaPart1 (A : Subgroup X) : Prop where
  A_le : A ≤ EgenX A
  comm_A : ∀ x ∈ EgenX A, ∀ a ∈ A, x * a = a * x
  pgroup : IsPGroup 2 (EgenX A)
  class_two : ∀ x ∈ EgenX A, ∀ y ∈ EgenX A, ∀ z ∈ EgenX A, ⁅⁅x, y⁆, z⁆ = 1
  six_two : ∀ {g h : X}, InOmegaA A g → InOmegaA A h → ∀ {x : X}, x ∈ conjSubgroup g A →
    x ≠ 1 → (∀ y ∈ conjSubgroup h A, x * y = y * x) ∨
      (∀ a ∈ A, ∃ y ∈ conjSubgroup h A, y * x * y⁻¹ = a * x)
  six_three : ⁅EgenX A, EgenX A⁆ ≠ ⊥ → ⁅EgenX A, EgenX A⁆ = A
  conj : ∀ g : X, conjSubgroup g (EgenX A) = ⨆ (h : X)
    (_ : ∀ z ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, z * y = y * z), conjSubgroup h A

structure OmegaPart2 (A : Subgroup X) : Prop where
  exists_noncomm : ⁅EgenX A, EgenX A⁆ ≠ ⊥ → ∀ {g : X}, InOmegaA A g → conjSubgroup g A ≠ A →
    ∀ {x : X}, x ∈ conjSubgroup g A → x ≠ 1 →
      ∃ h : X, InOmegaA A h ∧ ∃ y ∈ conjSubgroup h A, x * y ≠ y * x
  six_four : ⁅EgenX A, EgenX A⁆ ≠ ⊥ → ∀ {g : X}, InOmegaA A g → conjSubgroup g A ≠ A →
    ∀ {x : X}, x ∈ conjSubgroup g A → x ≠ 1 → ∀ a ∈ A, ∃ y : X, y * x * y⁻¹ = a * x
  six_four_gen : ⁅EgenX A, EgenX A⁆ ≠ ⊥ → ∀ {g h : X}, conjSubgroup g A ≠ conjSubgroup h A →
    (∀ z ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, z * y = y * z) →
    ∀ {y : X}, y ∈ conjSubgroup h A → y ≠ 1 → ∀ u ∈ conjSubgroup g A, ∃ w : X, w * y * w⁻¹ = u * y

structure EndLinModel (X : Type) [Group X] (H A : Subgroup X) : Prop where
  out : ∃ (K : Type) (_ : Field K) (E : Type) (_ : AddCommGroup E) (_ : Module K E)
    (act : X →* Equiv.Perm E) (ψ : E →ₗ[K] E),
    Function.Injective act ∧ (∀ (g : X) (e e' : E), act g (e + e') = act g e + act g e') ∧
    (∀ g : X, ∃ σ : K ≃+* K, ∀ (c : K) (e : E), act g (c • e) = σ c • act g e) ∧
    (∀ h ∈ H, ∀ (c : K) (e : E), act h (c • e) = c • act h e) ∧
    (∀ a ∈ A, ∃ c : K, ∀ e : E, act a e = e + c • ψ e)

variable [Finite X]

structure EndgameHyp (X : Type) [Group X] [Finite X] (A R N H : Subgroup X) (t : X) : Prop where
  o2 : pCore 2 X = ⊥
  H_normal : H.Normal
  A_le_R : A ≤ R
  R_le_H : R ≤ H
  t_mem : t ∈ A
  t_ne : t ≠ 1
  A_sq : ∀ a ∈ A, a * a = 1
  A_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  A_cent : ∀ a ∈ A, ∀ r ∈ R, a * r = r * a
  cent_le : ∀ x ∈ R, (∀ r ∈ R, x * r = r * x) → x ∈ A
  A_card : ∃ b : ℕ, 2 ≤ b ∧ Nat.card A = 2 ^ b
  N_le : N ≤ R
  N_normal : (N.subgroupOf R).Normal
  N_pgroup : IsPGroup 2 N
  N_gen : ∃ L : Subgroup X, (∀ x ∈ L, ∀ y ∈ L, x * y = y * x) ∧
    N = ⨆ (h : X) (_ : h ∈ R), conjSubgroup h L ⊓ N
  N_large : Nat.card A < Nat.card N
  F0 : ∀ c : X, c * t = t * c →
    c ∈ Subgroup.normalizer (R : Set X) ∧ c ∈ Subgroup.normalizer (N : Set X)
  F5 : ∀ Y : Subgroup X, Y.Normal → Y ≤ H → Odd (Nat.card Y) → Y = ⊥
  N1 : CommAllOf A
  N2 : CentOneOf H A
  comps : CompSimple X
  count : ∃ F : Finset (Subgroup X), F.card ≤ 3 ∧ ∀ C : Subgroup X, IsComponent C → C ∈ F
  quot : ∃ (S : Type) (_ : Group S) (π : ↥R →* S), Function.Surjective π ∧
    (∀ r : ↥R, π r = 1 ↔ (r : X) ∈ N) ∧ IsSimpleGroup S ∧ 16 ∣ Nat.card S ∧
    ∀ p : ℕ, p.Prime → p ∣ Nat.card A ^ 2 + 1 → p ∣ Nat.card S

end Endgame

end CFSG.RankThree.GF2n.Stroth80

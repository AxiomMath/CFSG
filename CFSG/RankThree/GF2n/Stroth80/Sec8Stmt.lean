module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth81Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → Conc81a hc t ∨ Conc81b hc t r

@[expose] def Stroth82Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → Conc81a hc t

@[expose] def Step81VanishStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ¬ Conc81a hc t →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → ∀ v ∈ Sec8V1 M Q Z B t r, ⁅x, v⁆ ∈ Z

@[expose] def Step81TypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ¬ Conc81a hc t →
    (∃ x : G, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧
      ∃ w ∈ Sec8W1 M Q Z B t r, ⁅x, w⁆ ∉ Sec8V1 M Q Z B t r) → SpMNat hc t 2

@[expose] def Step81CloseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (r : G), Close81Hyp hc n t r → False

@[expose] def Close81EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (r : G), Close81Hyp hc n t r → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0

@[expose] def Close81SylowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G) (r : G), Close81Hyp hc n t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∃ P : Sylow 2 (Mbar M Q),
      P.toSubgroup ≤ Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q))

@[expose] def Sec8TIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)

@[expose] def Close8FinalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t → ¬ Conc81a hc t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    (∃ P : Sylow 2 (Mbar M Q),
      P.toSubgroup ≤ Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q))) →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0 → False

@[expose] def Sec8AExistsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∃ r : G, Sec7A hc t r

@[expose] def Sec8InvStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ ρ ∈ Rt M (LB M Q B) t,
      conjSubgroup ρ (Sec8V1 M Q Z B t r) = Sec8V1 M Q Z B t r ∧
        conjSubgroup ρ (Sec8W1 M Q Z B t r) = Sec8W1 M Q Z B t r

@[expose] def Sec83UpperStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (m : ℕ), Sec5Hyp hc n t → 2 ≤ m → SpMNat hc t m →
    ∀ s ∈ Rt M (LB M Q B) t, (∀ ρ ∈ Rt M (LB M Q B) t, ⁅s, ρ⁆ ∈ Q) →
      Nat.card ↥(Ut Q Z s) ≤ Nat.card Z ^ (2 * m + 1)

@[expose] def Sec83LowerStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ z ∈ LB M Q B,
    Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z z) ^ 2 *
        Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z) ≤
      Nat.card ↥(Ut Q Z z) * Nat.card Z * Nat.card ↥(Sec8V1 M Q Z B t r)

@[expose] def Sec83TypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (m : ℕ) (K : Type) [Field K] [Finite K]
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
    Sec5Hyp hc n t → Sec7A hc t r → Sec8Pts hc t r m K φ u u' →
    ∀ (z : G) (hz : z ∈ Rt M (LB M Q B) t), z ∈ LB M Q B → z ∉ hc.CN t →
      (SpNonA2 (φ ⟨z, hz⟩) →
        Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z z) = Nat.card Z ^ 2 ∨
          Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z z) = Nat.card Z ^ 3) ∧
      (¬ SpNonA2 (φ ⟨z, hz⟩) →
        Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z z) = Nat.card Z ^ 3)

@[expose] def Sec83FixedStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (m : ℕ) (K : Type) [Field K] [Finite K]
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
    Sec5Hyp hc n t → Sec7A hc t r → Sec8Pts hc t r m K φ u u' →
    ∀ (z : G) (hz : z ∈ Rt M (LB M Q B) t), z ∈ LB M Q B → z ∉ hc.CN t →
      SpNonA2 (φ ⟨z, hz⟩) →
      Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z) ^ 2 =
        Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card ↥(Sec8W1 M Q Z B t r)

@[expose] def Sec83A2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
    (t r : G) (m : ℕ) (K : Type) [Field K] [Finite K]
    (φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K) (u u' : Fin m ⊕ Fin m → K),
    Sec5Hyp hc n t → Sec7A hc t r → Sec8Pts hc t r m K φ u u' →
    ∀ (z : G) (hz : z ∈ Rt M (LB M Q B) t), z ∈ LB M Q B → z ∉ hc.CN t →
      ¬ SpNonA2 (φ ⟨z, hz⟩) →
      Nat.card ↥(Sec8V1 M Q Z B t r) ^ 3 * Nat.card ↥(Sec8W1 M Q Z B t r) ≤
        Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z) ^ 4

@[expose] def Sec83SevenStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → SpMNat hc t 2 → n ≠ 7

end CFSG.RankThree.GF2n.Stroth80

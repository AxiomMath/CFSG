module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth76Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2

@[expose] def Stroth77Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → Conc71abcd hc n t

@[expose] def Stroth710Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∃ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B ∧ conjSubgroup g Z0 ≠ Z0

@[expose] def Stroth711StrongStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q

@[expose] def Stroth712Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) = pCore 2 ↥(bar M Q (NormH0 M Z Z0))

@[expose] def Stroth713Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → ¬ OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))

@[expose] def Step713O2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → ¬ OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    pCore 2 ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))

@[expose] def Stroth714Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 16

@[expose] def Stroth715Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 4 →
    SubConfig M Q Z (hc.CN t)

@[expose] def Sec7SylowLBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∃ P : Sylow 2 (Mbar M Q), P.toSubgroup ≤
      Subgroup.normalizer ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q))

@[expose] def Sec7EndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    (∃ P : Sylow 2 (Mbar M Q),
      P.toSubgroup ≤ Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q))) →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0 → False

@[expose] def Step76EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → ¬ OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0

@[expose] def Step77OneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z

@[expose] def Step77TwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    LB M Q B ⊓ conjSubgroup g (LB M Q B) = Q

@[expose] def Step77EndStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M (LB M Q B ⊓ hc.CN t) (LB M Q B) → StronglyClosedMod M Z0 (LB M Q B) →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z →
    LB M Q B ⊓ conjSubgroup g (LB M Q B) = Q → False

@[expose] def Sec7NOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ m : ℕ, 2 ≤ m → (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) →
    Nat.card ↥(hc.CN t) * Nat.card Z ^ (4 * m) = Nat.card Q ^ 2

@[expose] def Sec7WVOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ m : ℕ, 2 ≤ m →
    (OmegaMinusNat hc t m → ∃ y : ℕ, 1 ≤ y ∧ 2 * n = 4 * m + y * 2 ^ m) ∧
    (OmegaPlusNat hc t m → 3 ≤ m → ∃ y : ℕ, 1 ≤ y ∧ 2 * n = 4 * m + y * 2 ^ (m - 1))

@[expose] def Step78IneqStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → Conc71a hc t → ∀ m : ℕ, 2 ≤ m →
    (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) → 2 * n + 16 ≤ 12 * m

@[expose] def Sec7WVGeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 3 → 10 ≤ n

@[expose] def Sec79MinOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Z0 → ∀ m : ℕ, 2 ≤ m →
    (OmegaMinusNat hc t m → Nat.card Z0 * Nat.card Z ^ (2 ^ m) ≤ Nat.card A) ∧
    (OmegaPlusNat hc t m → 3 ≤ m → Nat.card Z0 * Nat.card Z ^ (2 ^ (m - 1)) ≤ Nat.card A)

@[expose] def Step710EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    (OmegaMinusNat hc t 3 ∨ OmegaPlusNat hc t 3 ∨ OmegaPlusNat hc t 4) →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0) →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0

@[expose] def Step714NotTwelveStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 4 → n = 12 → False

@[expose] def Step715ZNStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsCentrePre Z0 (hc.CN t) Q

@[expose] def Step715Hyp79Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaPlusNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → IsCentrePre Z0 (hc.CN t) Q →
    SubConfigHyp79 M Q Z (hc.CN t)

@[expose] def OmegaSignStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (t : G) (m : ℕ),
    2 ≤ m → OmegaPlusNat hc t m → OmegaMinusNat hc t m → False

@[expose] def Sec717L (hc : Ctx M Q Z B) (t : G) (Z0 L : Subgroup G) : Prop :=
  Q ≤ L ∧ L ≤ hc.CN t ∧ Nat.card L = Nat.card Q * Nat.card Z ^ 5 ∧
    (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r L = L) ∧ (∀ x ∈ L, ∀ y ∈ L, ⁅x, y⁆ ∈ Q) ∧ Z0 ≤ L

@[expose] def Step717CaseAStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ L : Subgroup G, Sec717L hc t Z0 L → (∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L) →
    FStarL6 M Q Z

@[expose] def Step717MaxAbStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (∀ L : Subgroup G, Sec717L hc t Z0 L → ∃ k ∈ NormH0 M Z Z0, conjSubgroup k L ≠ L) →
    ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q

@[expose] def Step717NotUnitaryStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t → OmegaPlusNat hc t 3 →
    ¬ FStarU6 M Q Z

end CFSG.RankThree.GF2n.Stroth80

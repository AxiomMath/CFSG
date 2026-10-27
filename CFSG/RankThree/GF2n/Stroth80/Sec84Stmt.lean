module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth84Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q

@[expose] def Stroth85Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))

@[expose] def Step84CaseOneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → Conc83 hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (¬ ∀ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ν ∈ Subgroup.normalizer (Z0 : Set G)) →
    ⁅hc.CN t, hc.CN t⁆ ≤ Q → StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) → False

@[expose] def Step84CaseTwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ⁅hc.CN t, hc.CN t⁆ ≤ Q → StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t)

@[expose] def Step85F2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) = pCore 2 ↥(bar M Q (NormH0 M Z Z0))

@[expose] def Step85CNNormalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) ≤
      pCore 2 ↥(bar M Q (NormH0 M Z Z0))

@[expose] def Sec8ZtStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, s ∉ Q →
      Rt M (LB M Q B) s = Rt M (LB M Q B) t ∧ Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t

@[expose] def Stroth56SpStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t →
    ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z

@[expose] def Sec85FirstVConc (M Q Z B : Subgroup G) (t r x : G) : Prop :=
  (∀ v ∈ Sec8V1 M Q Z B t r, ⁅x, v⁆ ∈ Z) ∧
  (∀ w ∈ Sec8W1 M Q Z B t r, ⁅x, w⁆ ∈ Sec8V1 M Q Z B t r)

@[expose] def Sec85FirstConc (hc : Ctx M Q Z B) (t r x : G) : Prop :=
  (∀ ρ ∈ Rt M (LB M Q B) t, ⁅x, ρ⁆ ∈ hc.CN t) ∧ Sec85FirstVConc M Q Z B t r x

@[expose] def Step85FirstVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ inSubgroup (pCore 2) (NormH0 M Z Z0), (∀ ρ ∈ Rt M (LB M Q B) t, ⁅x, ρ⁆ ∈ hc.CN t) →
    Sec85FirstVConc M Q Z B t r x

@[expose] def Step85FirstStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ inSubgroup (pCore 2) (NormH0 M Z Z0), Sec85FirstConc hc t r x

@[expose] def Step85CommStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ inSubgroup (pCore 2) (NormH0 M Z Z0), Sec85FirstConc hc t r x → x ∉ hc.CN t →
    (∀ z ∈ Z0, ⁅z, x⁆ ∈ Q) → False

@[expose] def Step85SylowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ¬ ⁅hc.CN t, hc.CN t⁆ ≤ Q →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ inSubgroup (pCore 2) (NormH0 M Z Z0), x ∉ hc.CN t → (∃ z ∈ Z0, ⁅z, x⁆ ∉ Q) → False

@[expose] def Step85O2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    pCore 2 ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0))

@[expose] def Sec86ZCardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    Nat.card Z0 = Nat.card Q * Nat.card Z

@[expose] def Sec86MinOrderStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ A : Subgroup G, Z0 ≤ A → A ≤ hc.CN t →
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r A = A) → A ≠ Z0 → ∀ m : ℕ, 2 ≤ m →
      SpMNat hc t m → Nat.card Z0 * Nat.card Z ^ (2 ^ m) ≤ Nat.card A

@[expose] def Sec86IrredStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0

@[expose] def Sec86ConjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, ConjMod M Q s x →
      ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ x * (ν * s * ν⁻¹)⁻¹ ∈ Q

@[expose] def Sec86NormHStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ν ∉ Subgroup.normalizer (Z0 : Set G) →
    ∃ ν' ∈ H0 M Z, ν' ∈ Subgroup.normalizer (LB M Q B : Set G) ∧
      ν' ∉ Subgroup.normalizer (Z0 : Set G)

@[expose] def Sec86NormLBStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0

@[expose] def Tim81StrothSpStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0 →
    FStarU6 M Q Z ∨ ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0

@[expose] def Step86HypSubStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    (∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0) →
    SubConfigHyp79 M Q Z (hc.CN t)

@[expose] def Step86NotUnitaryStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec8Hyp hc n t → ¬ FStarU6 M Q Z

end CFSG.RankThree.GF2n.Stroth80

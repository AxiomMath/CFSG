module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

@[expose] def N1 (hc : Ctx M Q Z B) (t : G) : Subgroup G := LB M Q B ⊓ hc.CN t

@[expose] def IsSingV (M Q Z B : Subgroup G) (t u : G) : Prop :=
  ∃ ρ ∈ Rt M (LB M Q B) t, ∃ b ∈ B, u * (ρ * b * ρ⁻¹)⁻¹ ∈ Z

@[expose] def IsTypeA2 (M Q Z B : Subgroup G) (t x : G) : Prop :=
  Nat.card ↥(⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ ⊔ Z) = Nat.card Z ^ 3 ∧
    ∀ v ∈ Vt M (LB M Q B) B Z t, IsSingV M Q Z B t ⁅x, v⁆

@[expose] def Centre95 (hc : Ctx M Q Z B) (t : G) (Z0 : Subgroup G) : Prop :=
  Z0 ≤ LB M Q B ⊓ hc.CN t ∧ Q.relIndex Z0 = Nat.card Z ∧
    ∀ s ∈ Z0, s ∉ Q → ⁅Q, Subgroup.zpowers s⁆ ⊔ Z = Vt M (LB M Q B) B Z t

structure Cfg95 (hc : Ctx M Q Z B) (n : ℕ) (t : G) (Z0 : Subgroup G) : Prop where
  hs : Sec9Hyp hc n t
  h6 : 6 ≤ n
  hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q
  hbad : ∀ s ∈ Z0, ∀ g ∈ M, g * s * g⁻¹ ∈ LB M Q B → g * s * g⁻¹ ∈ hc.CN t
  hnsc : ∃ s ∈ Z0, ∃ g ∈ M, g * s * g⁻¹ ∈ LB M Q B ∧ g * s * g⁻¹ ∉ Z0
  centre : Centre95 hc t Z0

structure ZPair95 (hc : Ctx M Q Z B) (t : G) (Z0 : Subgroup G) (z : G) : Prop where
  mem : z ∈ M
  normL : conjSubgroup z (LB M Q B) = LB M Q B
  toN1 : ∀ c ∈ Z0, z * c * z⁻¹ ∈ LB M Q B ⊓ hc.CN t
  notN : ∃ c ∈ Z0, z * c * z⁻¹ ∉ Z0

@[expose] def One95 (hc : Ctx M Q Z B) (t : G) (Z0 : Subgroup G) : Prop :=
  ∀ g ∈ M, conjSubgroup g (N1 hc t) = N1 hc t → conjSubgroup g Z0 = Z0

@[expose] def Three95 (hc : Ctx M Q Z B) (t : G) (z : G) : Prop :=
  (N1 hc t < N1 hc t ⊔ conjSubgroup z (N1 hc t) ∧
      (N1 hc t).relIndex (N1 hc t ⊔ conjSubgroup z (N1 hc t)) ≤ Nat.card Z) ∧
    ∀ x ∈ conjSubgroup z (N1 hc t), x ∉ hc.CN t → IsTypeA2 M Q Z B t x

@[expose] def Five95 (hc : Ctx M Q Z B) (t : G) (z : G) : Prop :=
  Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ 3 ∧
    B ≤ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t) ∧
    (∀ u ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t),
      IsSingV M Q Z B t u) ∧
    (∀ u ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t),
      ∃ ρ ∈ conjSubgroup z (Rt M (LB M Q B) t), ∃ b ∈ B, u * (ρ * b * ρ⁻¹)⁻¹ ∈ Z) ∧
    ∀ x ∈ conjSubgroup z (N1 hc t), x ∉ hc.CN t →
      ⁅Vt M (LB M Q B) B Z t, Subgroup.zpowers x⁆ ⊔ Z =
        Vt M (LB M Q B) B Z t ⊓ conjSubgroup z (Vt M (LB M Q B) B Z t)

end HS9

@[expose] def Step95CentreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      HS9.Centre95 hc t Z0

@[expose] def Step95ChoiceStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Z0 : Subgroup G), HS9.Cfg95 hc n t Z0 → ∃ z : G, HS9.ZPair95 hc t Z0 z

@[expose] def Step95OneStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G)
    (Z0 : Subgroup G), HS9.Cfg95 hc n t Z0 → HS9.One95 hc t Z0

end CFSG.RankThree.GF2n.Stroth80

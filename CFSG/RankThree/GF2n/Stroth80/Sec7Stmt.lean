module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec39Rt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Stroth71Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → Conc71abcd hc n t ∨ Conc71e hc t

@[expose] def Stroth72Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, x ∈ LB M Q B → ConjMod M Q t x → x ∉ Z0 →
    ∀ z ∈ Z0, ∃ ν ∈ hc.CN t, ν * x * ν⁻¹ * (x * z)⁻¹ ∈ Q

@[expose] def Stroth73aStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ m ∈ M, m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
      m ∈ Subgroup.normalizer (Z0 : Set G)

@[expose] def Stroth73bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    Fgen M Q (LB M Q B) Z0 = Z0 ∨
      ∀ a ∈ Fgen M Q (LB M Q B) Z0, ∀ b ∈ Fgen M Q (LB M Q B) Z0,
        a ∉ Q → b ∉ Q → a ^ 2 ∈ Q → b ^ 2 ∈ Q → ConjMod M Q a b

@[expose] def Stroth73cStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (StronglyClosedMod M (LB M Q B ⊓ hc.CN t) (LB M Q B) →
      StronglyClosedMod M Z0 (LB M Q B)) ∧
    (OmegaMinusNat hc t 2 → StronglyClosedMod M (LB M Q B ⊓ hc.CN t) (LB M Q B) ∧
      StronglyClosedMod M Z0 (LB M Q B))

@[expose] def Sec7AExistsStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∃ r : G, Sec7A hc t r

@[expose] def Sec7CentreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, x ∈ Z0 ↔ x ∈ LB M Q B ∧ ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Z

@[expose] def Sec7CentreMpStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x ∈ Z0, x ∈ LB M Q B ∧ ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Z

@[expose] def Sec7NormZ0Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ m ∈ M, m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
      m ∈ Subgroup.normalizer (Z0 : Set G)

@[expose] def Sec7ZtStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, s ∉ Q →
      Rt M (LB M Q B) s = Rt M (LB M Q B) t ∧ Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t

@[expose] def Sec7ZVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ u ∈ Z0, u ∉ Q → Ut Q Z u = Vt M (LB M Q B) B Z t

@[expose] def Sec7CVStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ∀ x ∈ Q,
    x ∈ Vt M (LB M Q B) B Z t ↔ ∀ y ∈ LB M Q B ⊓ hc.CN t, ⁅y, x⁆ ∈ Z

@[expose] def Stroth56NatStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ OmegaMinusNat hc t 2 →
    ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      ∃ r ∈ Rt M (LB M Q B) t, conjSubgroup m B ⊔ Z = conjSubgroup r B ⊔ Z

@[expose] def Sec7ConjStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, ConjMod M Q s x →
      ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ x * (ν * s * ν⁻¹)⁻¹ ∈ Q

@[expose] def Sec7ConjOm4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, ∀ x ∈ LB M Q B, ConjMod M Q s x →
      ∃ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) ∧ x * (ν * s * ν⁻¹)⁻¹ ∈ Q

@[expose] def Sec73CardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    (∀ α ∈ LB M Q B ⊓ hc.CN t, Nat.card ↥(Ut Q Z α) ≤ Nat.card Z ^ 8) ∧
    (∀ β ∈ LB M Q B, β ∉ hc.CN t → Nat.card Z ^ 8 < Nat.card ↥(Ut Q Z β))

@[expose] def Sec7ZCardStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    Nat.card Z0 = Nat.card Q * Nat.card Z

@[expose] def Sec7CommNStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q → ⁅hc.CN t, hc.CN t⁆ ≤ Z0

@[expose] def Step72IndexStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ x : G, x ∈ LB M Q B → ConjMod M Q t x → x ∉ Z0 →
    Nat.card Z * Nat.card ↥(hc.CN t ⊓ CommQ hc.hyp.Q_normal.2 x) ≤ Nat.card ↥(hc.CN t)

@[expose] def Stroth73aNotOm4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → ¬ OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ m ∈ M, m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
      m ∈ Subgroup.normalizer (Z0 : Set G)

@[expose] def Stroth73aOm4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ m ∈ M, m ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) →
      m ∈ Subgroup.normalizer (Z0 : Set G)

@[expose] def Stroth73bTransStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    Fgen M Q (LB M Q B) Z0 ≠ Z0 →
    ∀ a ∈ Fgen M Q (LB M Q B) Z0, ∀ b ∈ Fgen M Q (LB M Q B) Z0, a ∉ Q → b ∉ Q →
      ∃ g ∈ M, g ∈ Subgroup.normalizer (Fgen M Q (LB M Q B) Z0 : Set G) ∧
        b * (g * a * g⁻¹)⁻¹ ∈ Q

@[expose] def Stroth73cNotOm4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → ¬ OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M (LB M Q B ⊓ hc.CN t) (LB M Q B) → StronglyClosedMod M Z0 (LB M Q B)

@[expose] def Stroth73cOm4Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M (LB M Q B ⊓ hc.CN t) (LB M Q B) ∧ StronglyClosedMod M Z0 (LB M Q B)

@[expose] def Step71VanishStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z

@[expose] def Step71TypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    (∃ x : G, ConjMod M Q t x ∧ ⁅x, t⁆ ∈ Q ∧
      ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    OmegaMinusNat hc t 2 ∨ OmegaPlusNat hc t 3 ∨ OmegaPlusNat hc t 4

@[expose] def Step71CloseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    (∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q →
      ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) → False

@[expose] def Close71Hyp (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop :=
  Sec7Hyp hc n t ∧ ¬ Conc71abcd hc n t ∧
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q →
      ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t

@[expose] def Egen (M Q Z0 : Subgroup G) : Subgroup G :=
  ⨆ (g : G) (_ : g ∈ M) (_ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q), conjSubgroup g Z0

@[expose] def Close71EStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Close71Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0

@[expose] def Close71TIStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Close71Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)

@[expose] def Close71SylowStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Close71Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∃ P : Sylow 2 (Mbar M Q),
      P.toSubgroup ≤ Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q))

@[expose] def Close71FinalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Close71Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    (∃ P : Sylow 2 (Mbar M Q),
      P.toSubgroup ≤ Subgroup.normalizer ((bar M Q Z0 : Subgroup (Mbar M Q)) : Set (Mbar M Q))) →
    ⁅Egen M Q Z0, Egen M Q Z0⁆ ≤ Z0 → False

end CFSG.RankThree.GF2n.Stroth80

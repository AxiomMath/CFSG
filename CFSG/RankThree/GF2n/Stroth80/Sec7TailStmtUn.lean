module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Defs
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def Tim81StrothUnStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G), Sec7Hyp hc n t →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    IsMaxAbNormalMod (NormH0 M Z Z0) Z0 Q →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    generalizedFitting ↥(bar M Q (NormH0 M Z Z0)) =
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (NormH0 M Z Z0)) →
    ¬ NormH0L M Z (LB M Q B) ≤ NormH0 M Z Z0 →
    ∀ k : ℕ, Nat.card ↥(hc.CN t) = Nat.card Q * Nat.card Z ^ k →
    (∃ m : ℕ, 2 * m - 3 = k ∧
      IsPSUModel m (Nat.card Z) ↥(generalizedFitting ↥(bar M Q (H0 M Z)))) ∨
    ∃ g ∈ M, conjSubgroup g Z0 ≤ hc.CN t ∧ conjSubgroup g Z0 ≠ Z0

@[expose] def Stroth716TypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec5Hyp hc n t → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t) →
    ((∃ m : ℕ, 4 ≤ m ∧ OmegaPlusNat hc t m) ∨ (∃ m : ℕ, 2 ≤ m ∧ OmegaMinusNat hc t m)) →
    SubConfig M Q Z (hc.CN t) ∨ (OmegaMinusNat hc t 3 ∧ FStarU6 M Q Z)

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

@[expose] def Stroth111bStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n →
    (∃ k m : ℕ, Odd m ∧ Nat.card ↥(Subgroup.centralizer (bar M Q (LB M Q B) : Set (Mbar M Q)) ⊓
        bar M Q (H0 M Z)) = 2 ^ k * m ∧ m ∣ Nat.card Z - 1) ∧
    ∀ h ∈ H0 M Z, (∀ x ∈ LB M Q B, ⁅h, x⁆ ∈ Q) → (∀ b ∈ B, ⁅h, b⁆ ∈ Z) →
      ∃ k : ℕ, h ^ 2 ^ k ∈ Q

@[expose] def Stroth112Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    (∃ e₀ ∈ Ebar M Q Z B, Ebar M Q Z B = {e | ∃ x ∈ Xbar M Q Z B, e = x * e₀ * x⁻¹}) ∧
    ∀ e₁ ∈ Ebar M Q Z B, ∀ e₂ ∈ Ebar M Q Z B,
      (orderOf (e₁ * e₂) = 2 ∨ orderOf (e₁ * e₂) = 4 ∨ Odd (orderOf (e₁ * e₂))) ∧
      (orderOf (e₁ * e₂) = 4 → (e₁ * e₂) ^ 2 ∈ Ebar M Q Z B)

@[expose] def StrothA2LineStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ),
    Width Q Z n → 2 < n → ∀ a ∈ LB M Q B, IsA2 Q Z a → B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z

@[expose] def Stroth114Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
      ∃ f : ↥(Subgroup.centralizer (Xbar M Q Z B : Set (Mbar M Q)) ⊓ bar M Q (H0 M Z)) →*
        GL (Fin 2) K, Function.Injective f

@[expose] def Stroth115Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → (∃ a ∈ LB M Q B, IsA2 Q Z a) →
    ∃ (t : StatedLieTag) (n' f : ℕ), t ≠ .twistedF4 ∧ t ≠ .Tits ∧ StatedLieAdmissible t n' 2 f ∧
      CFSG.Blueprint.LieModel (↥(Xbar M Q Z B) ⧸ Subgroup.center ↥(Xbar M Q Z B)) t n' 2 f

end CFSG.RankThree.GF2n.Stroth80

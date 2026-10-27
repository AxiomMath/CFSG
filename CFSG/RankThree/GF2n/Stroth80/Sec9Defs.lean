module

public import CFSG.RankThree.GF2n.Stroth80.Sec12Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec9Hyp (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop where
  toSec5 : Sec5Hyp hc n t
  plus4 : OmegaPlusNat hc t 2
  large : ∀ τ ∈ LB M Q B, τ ∉ Q → Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN τ)

omit [Finite G] in
@[expose] def IsDirectSumSec (P I A₁ A₂ : Subgroup G) : Prop :=
  I ≤ A₁ ∧ A₁ ≤ P ∧ I ≤ A₂ ∧ A₂ ≤ P ∧ A₁ ⊔ A₂ = P ∧ A₁ ⊓ A₂ = I

omit [Finite G] in
@[expose] def IsDirectProdQuot (R R₀ Y Q : Subgroup G) : Prop :=
  Q ≤ R₀ ∧ R₀ ≤ R ∧ Q ≤ Y ∧ Y ≤ R ∧ R₀ ⊔ Y = R ∧ R₀ ⊓ Y = Q ∧ ∀ a ∈ R₀, ∀ y ∈ Y, ⁅a, y⁆ ∈ Q

@[expose] def Sec9R0 (hc : Ctx M Q Z B) (t x : G) : Subgroup G :=
  hc.CN t ⊔ ⨆ (ρ : G) (_ : ρ ∈ Rt M (LB M Q B) t), Subgroup.zpowers (ρ * x * ρ⁻¹)

omit [Finite G] in
@[expose] def WeaklyClosedInCent (M Q Z0 : Subgroup G) : Prop :=
  ∀ g ∈ M, (∀ x ∈ Z0, ∀ y ∈ Z0, ⁅g * x * g⁻¹, y⁆ ∈ Q) → ∀ x ∈ Z0, g * x * g⁻¹ ∈ Z0

omit [Finite G] in
structure Sec9T1 (M Q Z0 : Subgroup G) (s z : G) : Prop where
  s_mem : s ∈ Z0
  z_mem : z ∈ M
  comm : ∀ y ∈ Z0, ⁅z * s * z⁻¹, y⁆ ∈ Q
  not_mem : z * s * z⁻¹ ∉ Z0

theorem Sec9Hyp.mem {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec9Hyp hc n t) : t ∈ LB M Q B :=
  h.toSec5.mem

theorem Sec9Hyp.notQ {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec9Hyp hc n t) : t ∉ Q :=
  h.toSec5.notQ

theorem Sec9Hyp.large_t {hc : Ctx M Q Z B} {n : ℕ} {t : G} (h : Sec9Hyp hc n t) :
    Nat.card Q * Nat.card Z < Nat.card ↥(hc.CN t) :=
  h.large t h.mem h.notQ

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Quasithin.Background.G64Statement
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def IsMinNormalIn {Γ : Type*} [Group Γ] (H K : Subgroup Γ) : Prop :=
  K ≤ H ∧ (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) ∧ K ≠ ⊥ ∧
    ∀ K' : Subgroup Γ, K' ≤ K → (∀ h ∈ H, ∀ k ∈ K', h * k * h⁻¹ ∈ K') → K' = ⊥ ∨ K' = K

@[expose] def Input15358Two : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H K : Subgroup (MulAut W)) (a : MulAut W) (W₁ W₂ : Subgroup W),
      G64.IsQuotientOfSQTKCat ↥H → pCoreOf 2 H = ⊥ → IsIrrOn153 H ⊤ → IsMinNormalIn H K →
      ¬ (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) →
      a ∈ H → a ≠ 1 → a ^ 2 = 1 →
      (∃ T' : Subgroup (MulAut W), IsSylowTwoOf T' H ∧ a ∈ T' ∧ ∀ x ∈ T', x * a = a * x) →
      IsIntDirect W₁ W₂ ⊤ → IsIrrOn153 K W₁ → IsIrrOn153 K W₂ → Nat.card ↥W₁ = Nat.card ↥W₂ →
      8 ≤ Nat.card ↥W₁ → 8 ≤ Nat.card ↥W₂ →
      (∀ w ∈ W₁, a w ∈ W₁) → (∀ w ∈ W₂, a w ∈ W₂) →
      Nat.card ↥(commIn153 (Subgroup.zpowers a) W₁) = 2 → Nat.card ↥(commIn153 (Subgroup.zpowers a) W₂) = 2 →
      (∀ h ∈ H, orderOf h = 3 →
        ∃ r ∈ commV (Subgroup.zpowers a), h r ∉ commV (Subgroup.zpowers a)) →
      ∃ π : ↥(StatedSL 3 (ZMod 2)) →* ↥K, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π

@[expose] def Input15358G93 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H K A : Subgroup (MulAut W)) (a : MulAut W) (m : ℕ),
      G64.IsQuotientOfSQTKCat ↥H → pCoreOf 2 H = ⊥ → IsIrrOn153 H ⊤ → IsMinNormalIn H K →
      ¬ (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) → IsIrrOn153 K ⊤ →
      A ≤ H → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x ^ 2 = 1) → Nat.card ↥A = 2 ^ m →
      Nat.card W ≤ 2 ^ (2 * (m + 1)) → (∃ x ∈ A, ∃ k ∈ K, x * k ≠ k * x) →
      a ∈ A → a ≠ 1 → a ^ 2 = 1 → Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2 → 2 ^ 6 ≤ Nat.card W →
      (∃ T' : Subgroup (MulAut W), IsSylowTwoOf T' H ∧ a ∈ T' ∧ (∀ x ∈ T', x * a = a * x) ∧
        Nat.card ↥(fixV T') = 2 ∧ ∀ h ∈ H, orderOf h = 3 → ∃ z ∈ fixV T', h z ≠ z) →
      False

end CFSG.Quasithin

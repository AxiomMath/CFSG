module

public import CFSG.Quasithin.Background.A3Structure315Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

@[expose] def A315Char2List (X : Type) [Group X] : Prop :=
  (∃ f : ℕ, (2 ≤ f ∧ IsPSL 2 2 f X) ∨ (1 ≤ f ∧ IsPSL 3 2 f X) ∨ (2 ≤ f ∧ IsPSU 3 2 f X) ∨
      (2 ≤ f ∧ IsPSp4 2 f X) ∨ (2 ≤ f ∧ IsG2 2 f X) ∨ (1 ≤ f ∧ Is3D4 2 f X) ∨
      (Odd f ∧ 3 ≤ f ∧ Is2F4 f X) ∨ (Odd f ∧ 3 ≤ f ∧ IsSz f X)) ∨
    IsTits X

@[expose] def A315LieClass (X : Type) [Group X] : Prop :=
  A315Char2List X ∨ (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 X)

@[expose] def A315SporadicList (X : Type) [Group X] : Prop :=
  ∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru) ∧ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier s)

@[expose] def A315AltFact : Prop :=
  ∀ (G : Type) [Group G] (L T B : Subgroup G), A315Hyp L T B →
    ∀ n : ℕ, 5 ≤ n → n ≤ 8 → ¬ IsAlt n ↥L

@[expose] def A315L2Fact : Prop :=
  ∀ (G : Type) [Group G] (L T B : Subgroup G), A315Hyp L T B →
    ∀ p e : ℕ, p.Prime → p ≠ 2 → 1 ≤ e → e ≤ 2 → IsPSL 2 p e ↥L → A315Case1 L T B

@[expose] def A315L3Fact : Prop :=
  ∀ (G : Type) [Group G] (L T B : Subgroup G), A315Hyp L T B → IsMulCommutative ↥B →
    ∀ (δ : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 δ p 1 ↥L →
      A315Case2 L T B ∨ A315Case3 L T B

@[expose] def A315L3RFact : Prop :=
  ∀ (G : Type) [Group G] (L T B : Subgroup G), A315Hyp L T B → ¬ IsMulCommutative ↥B →
    ∀ (δ : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 δ p 1 ↥L →
      ∀ r : ℕ, r.Prime → 3 < r → IsPGroup r ↥B → B ≤ L → False

@[expose] def A315SporadicFact : Prop :=
  ∀ (G : Type) [Group G] (L T B : Subgroup G), A315Hyp L T B → A315SporadicList ↥L →
    A315Case4 L T B

end CFSG.Quasithin

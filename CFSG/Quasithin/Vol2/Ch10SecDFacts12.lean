module

public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.Background.E3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Quasithin

@[expose] def RankBoundAut {W : Type*} [Group W] (Λ : Subgroup (MulAut W)) (r : ℕ) : Prop :=
  ∀ E : Subgroup (MulAut W), E ≤ Subgroup.normalizer (Λ : Set (MulAut W)) →
    IsElemAbelian 2 E → Nat.card E ≤ 2 ^ r

@[expose] def Fact12L2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Λ : Subgroup (MulAut W)) (n : ℕ), 1 < n → commV Λ = ⊤ →
      BinaryNaturalSL Λ ⊤ (fixV Λ) 2 n → RankBoundAut Λ n

@[expose] def Fact12A5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Λ : Subgroup (MulAut W), commV Λ = ⊤ → fixV Λ = ⊥ → AlternatingNatural Λ ⊤ ⊥ 5 →
      Nat.card W = 2 ^ 4 ∧ RankBoundAut Λ 2 ∧
      ∀ E : Subgroup (MulAut W), E ≤ Subgroup.normalizer (Λ : Set (MulAut W)) →
        IsElemAbelian 2 E → E ≠ ⊥ → ∀ q : ℕ,
          (∀ B : Subgroup (MulAut W), B ≤ E → E3.mQuot E B < q → fixV B = fixV E) → q ≤ 1

@[expose] def Fact12O4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Λ : Subgroup (MulAut W)) (n : ℕ), 1 < n → commV Λ = ⊤ → fixV Λ = ⊥ →
      BinaryOrthogonalFour Λ ⊤ ⊥ n → Nat.card W = 2 ^ (4 * n) ∧ RankBoundAut Λ (2 * n)

@[expose] def Fact12WW : Prop :=
  ∀ (W W₁ : Type) [CommGroup W] [Finite W] [CommGroup W₁] [Finite W₁], (∀ w : W, w ^ 2 = 1) →
    ∀ ι : W₁ →* W, Function.Injective ι → ∀ (Λ : Subgroup (MulAut W)) (Λ₁ : Subgroup (MulAut W₁)),
      BinaryNaturalSL Λ₁ ⊤ ⊥ 3 1 →
      (∀ x ∈ Λ, ∃ y ∈ Λ₁, ∀ w, x (ι w) = ι (y w)) →
      (∀ y ∈ Λ₁, ∃ x ∈ Λ, ∀ w, x (ι w) = ι (y w)) →
      (∀ x ∈ Λ, (∀ w, x (ι w) = ι w) → x = 1) →
      ∀ s ∈ Subgroup.normalizer (Λ : Set (MulAut W)),
        ι.range ⊔ ι.range.map (s : MulAut W).toMonoidHom = ⊤ →
        ι.range ⊓ ι.range.map (s : MulAut W).toMonoidHom = ⊥ → RankBoundAut Λ 3

@[expose] def Fact12Sz : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (Λ : Subgroup (MulAut W)) (n : ℕ), commV Λ = ⊤ → fixV Λ = ⊥ →
      BinaryNaturalSz Λ ⊤ ⊥ n → RankBoundAut Λ n

end CFSG.Quasithin.Vol2.Ch10.SecD

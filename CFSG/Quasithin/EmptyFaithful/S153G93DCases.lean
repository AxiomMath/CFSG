module

public import CFSG.Quasithin.EmptyFaithful.S153G93DUtil
public import CFSG.Quasithin.Background.F918P0
public import CFSG.Quasithin.Background.B4ModelsSporadic

public section

namespace CFSG.Quasithin

namespace S153G93D

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def CovSL3 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)) (n : ℕ),
    BinaryNaturalSL J ⊤ ⊥ 3 n → CovOrder3 J

@[expose] def CovSp4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)) (n : ℕ),
    BinaryNaturalSp4 J ⊤ ⊥ n → CovOrder3 J

@[expose] def CovAlt7 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)),
    AlternatingNatural J ⊤ ⊥ 7 → CovOrder3 J

@[expose] def CovSym7 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)),
    SymmetricNatural J ⊤ ⊥ 7 → CovOrder3 J

@[expose] def CovL42 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)),
    SLExteriorTwo J ⊤ ⊥ 4 → CovOrder3 J

@[expose] def CovG2One : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)),
    G2Natural J ⊤ ⊥ 1 → CovOrder3 J

@[expose] def CovG2Der : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)),
    G2NaturalDerived J ⊤ ⊥ 1 → CovOrder3 J

structure ModelSizes : Prop where
  sl : ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)) (d a : ℕ),
    BinaryNaturalSL J ⊤ ⊥ d a → Nat.card W = 2 ^ (d * a)
  sp4 : ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)) (a : ℕ),
    BinaryNaturalSp4 J ⊤ ⊥ a → Nat.card W = 2 ^ (4 * a)
  alt : ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)) (n : ℕ),
    AlternatingNatural J ⊤ ⊥ n → Nat.card W ≤ 2 ^ (n - 1)
  sym : ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)) (n : ℕ),
    SymmetricNatural J ⊤ ⊥ n → Nat.card W ≤ 2 ^ (n - 1)
  a7 : ∀ (W : Type) [CommGroup W] [Finite W] (J : Subgroup (MulAut W)),
    A7Four J ⊤ ⊥ → Nat.card W = 2 ^ 4

@[expose] def SL2Cent : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (P : Subgroup ↥(StatedSL 2 F)),
    IsSylowTwoOf P ⊤ → ∀ α : MulAut ↥(StatedSL 2 F), (∀ x ∈ P, α x = x) →
      ∃ p ∈ P, ∀ g : ↥(StatedSL 2 F), α g = p * g * p⁻¹

@[expose] def OneSL2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → (∃ n, BinaryNaturalSL K ⊤ ⊥ 2 n) → False

@[expose] def OneG2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → (∃ n, 2 ≤ n ∧ G2Natural K ⊤ ⊥ n) → False

@[expose] def OneExtSq5 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → G₀ = K → SLExteriorTwo K ⊤ ⊥ 5 → False

@[expose] def OneSU3 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → (∃ m, BinaryNaturalSU3 K ⊤ ⊥ m) → False

@[expose] def OneSz : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → (∃ f, BinaryNaturalSz K ⊤ ⊥ f) → False

@[expose] def OneOrth4 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → (∃ m, 1 ≤ m ∧ BinaryOrthogonalFour K ⊤ ⊥ m) → False

@[expose] def OneM22Code : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → MathieuCode22 K ⊤ ⊥ → False

@[expose] def OneHat : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (G₀ K S : Subgroup (MulAut W)) (a : MulAut W) (z : W),
    Ctx1 W G₀ K a S z → (TripleA6Six K ⊤ ⊥ ∨ Mhat22Twelve K ⊤ ⊥) → False

structure OneCases : Prop where
  covSL3 : CovSL3
  covSp4 : CovSp4
  covAlt7 : CovAlt7
  covSym7 : CovSym7
  covL42 : CovL42
  covG2One : CovG2One
  covG2Der : CovG2Der
  sizes : ModelSizes
  sl2 : OneSL2
  g2 : OneG2
  extSq5 : OneExtSq5
  su3 : OneSU3
  sz : OneSz
  orth4 : OneOrth4
  m22code : OneM22Code
  hat : OneHat

structure TwoCtx (W : Type) [CommGroup W] [Finite W] (K L₁ L₂ : Subgroup (MulAut W)) (a : MulAut W)
    (S : Subgroup (MulAut W)) : Prop extends Ctx2 W K a S where
  simple₁ : IsSimpleGroup ↥L₁
  simple₂ : IsSimpleGroup ↥L₂
  nab₁ : ∃ x y : ↥L₁, x * y ≠ y * x
  nab₂ : ∃ x y : ↥L₂, x * y ≠ y * x
  comm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x
  sup : K = L₁ ⊔ L₂
  inf : L₁ ⊓ L₂ = ⊥
  aL₁ : ∀ x ∈ L₁, a * x * a⁻¹ ∈ L₁
  aL₂ : ∀ x ∈ L₂, a * x * a⁻¹ ∈ L₂
  syl₁ : IsSylowTwoOf (S ⊓ L₁) L₁
  syl₂ : IsSylowTwoOf (S ⊓ L₂) L₂

@[expose] def TwoOmega : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (K L₁ L₂ S : Subgroup (MulAut W)) (a : MulAut W),
    TwoCtx W K L₁ L₂ a S → (∃ n, IsPSL 2 2 n ↥L₁ ∧ Omega4PlusModule K n) → False

@[expose] def TwoTensor : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (K L₁ L₂ S : Subgroup (MulAut W)) (a : MulAut W),
    TwoCtx W K L₁ L₂ a S → (IsPSL 3 2 1 ↥L₁ ∧ TensorNatL32 K) → False

structure TwoCases : Prop where
  omega : TwoOmega
  tensor : TwoTensor

end S153G93D

end CFSG.Quasithin

module

public import CFSG.Quasithin.H13.AS91Sec5Defs
public import CFSG.Quasithin.Recognition.UniquenessSystemCriterion

public section

namespace CFSG.Quasithin.H13.AS91

open Subgroup CFSG.Open MulAction CFSG.Quasithin.Asc94
open scoped Pointwise

section HypV

variable {G : Type*} [Group G] {X : Type*} [MulAction G X]

@[expose] def autPres (A B : Subgroup G) (φ : ↥A ≃* ↥A) : Prop :=
  ∀ a : ↥A, (a : G) ∈ B ↔ ((φ a : ↥A) : G) ∈ B

@[expose] def autFix (A B : Subgroup G) (φ : ↥A ≃* ↥A) : Prop :=
  ∀ a : ↥A, (a : G) ∈ B → ((φ a : ↥A) : G) = a

@[expose] def autImage {A : Subgroup G} (ψ : ↥A ≃* ↥A) (C : Subgroup G) : Subgroup G :=
  ((C.subgroupOf A).map ψ.toMonoidHom).map A.subtype

@[expose] def conjSub (i : G) (C : Subgroup G) : Subgroup G := C.map (MulAut.conj i).toMonoidHom

@[expose] def dblSet (I : Subgroup G) (x y : X) : Set G :=
  ((I ⊓ stabilizer G x : Subgroup G) : Set G) *
    ((I ⊓ stabilizer G ({x, y} : Set X) : Subgroup G) : Set G) *
    ((I ⊓ stabilizer G x : Subgroup G) : Set G)

structure HypV (I : Subgroup G) (x y : X) : Prop where
  v1 : ∀ θ : ↥(I ⊓ stabilizer G x) ≃* ↥(I ⊓ stabilizer G x),
    ∃ (φ : ↥I ≃* ↥I) (ψ : ↥(stabilizer G x) ≃* ↥(stabilizer G x)),
      autPres I (I ⊓ stabilizer G x) φ ∧ autPres (stabilizer G x) (I ⊓ stabilizer G x) ψ ∧
      ∀ b : ↥(I ⊓ stabilizer G x),
        ((θ b : ↥(I ⊓ stabilizer G x)) : G) = totFun φ (totFun ψ (b : G))
  v2 : ∀ ψ : ↥(stabilizer G x) ≃* ↥(stabilizer G x),
    autPres (stabilizer G x) (I ⊓ stabilizer G x) ψ →
    ∃ ψ₁ ψ₂ : ↥(stabilizer G x) ≃* ↥(stabilizer G x),
      (∀ i ∈ I ⊓ stabilizer G x, ∃ j ∈ I ⊓ stabilizer G x,
        autImage ψ₁ (conjSub i (stabilizer G x ⊓ stabilizer G y)) =
          conjSub j (stabilizer G x ⊓ stabilizer G y)) ∧
      (∀ i ∈ I ⊓ stabilizer G x, ∃ j ∈ I ⊓ stabilizer G x,
        autImage ψ₁.symm (conjSub i (stabilizer G x ⊓ stabilizer G y)) =
          conjSub j (stabilizer G x ⊓ stabilizer G y)) ∧
      autFix (stabilizer G x) (I ⊓ stabilizer G x) ψ₂ ∧
      ∀ g : ↥(stabilizer G x), ((ψ g : ↥(stabilizer G x)) : G) = ψ₁ (ψ₂ g)
  v3 : ∀ φ : ↥I ≃* ↥I, autPres I (I ⊓ stabilizer G x) φ →
    ∃ φ₁ φ₂ : ↥I ≃* ↥I,
      (∀ d : ↥I, (d : G) ∈ dblSet I x y ↔ ((φ₁ d : ↥I) : G) ∈ dblSet I x y) ∧
      autFix I (I ⊓ stabilizer G x) φ₂ ∧
      ∀ i : ↥I, ((φ i : ↥I) : G) = φ₁ (φ₂ i)
  v4 : ∀ g ∈ I ⊓ stabilizer G x,
    g ∈ Subgroup.normalizer ((I ⊓ stabilizer G x ⊓ stabilizer G y : Subgroup G) : Set G) →
    g ∈ Subgroup.normalizer ((stabilizer G x ⊓ stabilizer G y : Subgroup G) : Set G)

end HypV

@[expose] def Stmt8_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y ∈ c.ptsL, y ≠ c.x0 → HypV c.G3 c.x0 y

@[expose] def Stmt8_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z)
    (G' : Type) [Group G'] [Finite G'] (z' : G') (_ : HypJ4 G' z') (c' : Loc49 G' z')
    (y : G ⧸ c.G1) (y' : G' ⧸ c'.G1), y ∈ c.ptsL → y ≠ c.x0 → y' ∈ c'.ptsL → y' ≠ c'.x0 →
    ∃ ζ : ↥c.G3 ≃* ↥c'.G3,
      ((stabilizer G c.x0).subgroupOf c.G3).map ζ.toMonoidHom =
        (stabilizer G' c'.x0).subgroupOf c'.G3 ∧
      ((stabilizer G ({c.x0, y} : Set (G ⧸ c.G1))).subgroupOf c.G3).map ζ.toMonoidHom =
        (stabilizer G' ({c'.x0, y'} : Set (G' ⧸ c'.G1))).subgroupOf c'.G3

@[expose] def Stmt8_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z)
    (G' : Type) [Group G'] [Finite G'] (z' : G') (_ : HypJ4 G' z') (c' : Loc49 G' z')
    (y : G ⧸ c.G1) (y' : G' ⧸ c'.G1), y ∈ c.ptsL → y ≠ c.x0 → y' ∈ c'.ptsL → y' ≠ c'.x0 →
    ∃ α : ↥(stabilizer G c.x0) ≃* ↥(stabilizer G' c'.x0),
      (c.G3.subgroupOf (stabilizer G c.x0)).map α.toMonoidHom =
        c'.G3.subgroupOf (stabilizer G' c'.x0) ∧
      ((stabilizer G y).subgroupOf (stabilizer G c.x0)).map α.toMonoidHom =
        (stabilizer G' y').subgroupOf (stabilizer G' c'.x0)

@[expose] def Stmt8_Kchar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ y ∈ c.ptsL, y ≠ c.x0 →
      ∀ φ : ↥(stabilizer G c.x0 ⊓ stabilizer G y) ≃* ↥(stabilizer G c.x0 ⊓ stabilizer G y),
        ∀ k : ↥(stabilizer G c.x0 ⊓ stabilizer G y), (k : G) ∈ c.K →
          ((φ k : ↥(stabilizer G c.x0 ⊓ stabilizer G y)) : G) ∈ c.K

@[expose] def Stmt8_Kaut : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    ∀ α : ↥c.K ≃* ↥c.K, (∀ k : ↥c.K, (k : G) ∈ c.G3 → α k = k) →
      ∃ w : G, w ∈ c.G3 ∧ w ∈ normalizer (c.K : Set G) ∧ (∀ i ∈ c.G3, w * i = i * w) ∧
        ∀ k : ↥c.K, ((α k : ↥c.K) : G) = w * k * w⁻¹

end CFSG.Quasithin.H13.AS91

module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter3section1.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Dimension.Finite

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter3section3

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open PFchapter3section1

/-!
# Basic interfaces for Peterfalvi, Part II, Chapter III, Section 3
-/


/-- The coherent coordinate and action model asserted by the Chapter III,
Section 3 proposition.  Chapter IV consumes this already-proved model as its
input; it contains no Chapter IV canonical maps or unitary conclusion. -/
@[expose] public def TypeBChapter3Data
    (G : Type*) [Group G] (K Q0 S W : Subgroup G) (s : G) : Prop :=
  ∃ (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2)
      (F : Subfield E)
      (theta : F ≃+* F) (sigma : E ≃+* E)
      (phi : E → E → E)
      (K1 W1 : Subgroup Eˣ)
      (S1 : Type) (_ : Group S1)
      (coord : S1 ≃
        {p : E × E //
          (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
            (theta ≠ 1 ∧ p.2 ∈ F)})
      (rho : (K ⊔ W : Subgroup G) →* MulAut S)
      (rho1 : (K1 ⊔ W1 : Subgroup Eˣ) →* MulAut S1)
      (sIso : S ≃* S1)
      (kwIso : (K ⊔ W : Subgroup G) ≃* (K1 ⊔ W1 : Subgroup Eˣ))
      (modelIso :
        SemidirectProduct S (K ⊔ W : Subgroup G) rho ≃*
          SemidirectProduct S1 (K1 ⊔ W1 : Subgroup Eˣ) rho1),
    Module.finrank F E = 2 ∧
      Nat.card F = Nat.card Q0 ∧
      Odd (orderOf theta) ∧
      (∀ a : F, sigma (a : E) = (theta a : F)) ∧
      (theta = 1 → ∀ x : E, sigma x = x ^ Nat.card F) ∧
      (∀ a : Eˣ, a ∈ K1 ↔
        ∃ b : Fˣ, (a : E) = ((b : F) : E)) ∧
      W1 ≠ ⊥ ∧
      (∀ a : Eˣ, a ∈ W1 → (a : E) ^ (Nat.card F + 1) = 1) ∧
      (∀ a : Eˣ, a ∈ W1 → sigma (a : E) = (a : E)⁻¹) ∧
      (theta = 1 → ∀ x y : E, phi x y = x * sigma y) ∧
      (theta ≠ 1 →
        (∀ x y : E, phi x y ∈ F) ∧
        (∀ x y z : E, phi (x + y) z = phi x z + phi y z) ∧
        (∀ x y z : E, phi x (y + z) = phi x y + phi x z) ∧
        (∀ a b : F, ∀ x y : E,
          phi ((a : E) * x) ((b : E) * y) =
            (a : E) * (theta b : F) * phi x y) ∧
        (∀ x : E, x ≠ 0 → phi x x ≠ 0)) ∧
      (∀ x y : S1,
        ((coord (x * y) :
            {p : E × E //
              (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) =
          ((coord x).1.1 + (coord y).1.1,
            (coord x).1.2 + (coord y).1.2 +
              phi (coord x).1.1 (coord y).1.1)) ∧
      (∀ a : (K ⊔ W : Subgroup G), ∀ x : S,
        ((rho a x : S) : G) =
          (a : G) * (x : G) * (a : G)⁻¹) ∧
      (∀ a : (K1 ⊔ W1 : Subgroup Eˣ), ∀ x : S1,
        ((coord (rho1 a⁻¹ x) :
            {p : E × E //
              (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) =
          (((a : Eˣ) : E) * (coord x).1.1,
            ((a : Eˣ) : E) * sigma ((a : Eˣ) : E) *
              (coord x).1.2)) ∧
      (∀ x : S,
        modelIso (SemidirectProduct.inl x) =
          SemidirectProduct.inl (sIso x)) ∧
      (∀ a : (K ⊔ W : Subgroup G),
        modelIso (SemidirectProduct.inr a) =
          SemidirectProduct.inr (kwIso a)) ∧
      Subgroup.map kwIso.toMonoidHom (K.subgroupOf (K ⊔ W)) =
        K1.subgroupOf (K1 ⊔ W1) ∧
      Subgroup.map kwIso.toMonoidHom (W.subgroupOf (K ⊔ W)) =
        W1.subgroupOf (K1 ⊔ W1) ∧
      ∃ hs : s ∈ S,
        ((coord (sIso ⟨s, hs⟩) :
            {p : E × E //
              (theta = 1 ∧ p.2 + sigma p.2 = p.1 * sigma p.1) ∨
                (theta ≠ 1 ∧ p.2 ∈ F)}) : E × E) = (0, 1)

/-- Hypothesis (C2). -/
public structure HypothesisC2
    (G : Type*) [Group G] (S W : Subgroup G) (t s : G) : Prop where
  S_type_B : IsSuzukiTwoTypeB S
  st_order_three : orderOf (s * t) = 3
  W_ne_bot : W ≠ ⊥

end PFchapter3section3
end CFSG.BenderSuzuki

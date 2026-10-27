module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open Matrix

@[expose] def orthReflSet (p m : ℕ) (f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p)) :
    Set (GL (Fin m) (ZMod p)) :=
  {g | ∃ v : Fin m → ZMod p, f v v = -2 ∧
    ∀ x, (g : Matrix (Fin m) (Fin m) (ZMod p)) *ᵥ x = x + f x v • v}

@[expose] def IsReflModel (p m : ℕ) (f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p))
    (X : Type) [Group X] (D : Set X) : Prop :=
  ∃ e : X ≃* ↥(Subgroup.closure (orthReflSet p m f)),
    ∀ d ∈ D, ((e d : GL (Fin m) (ZMod p))) ∈ orthReflSet p m f

@[expose] def IsReflQuotModel (p m : ℕ) (f : LinearMap.BilinForm (ZMod p) (Fin m → ZMod p))
    (X : Type) [Group X] (D : Set X) : Prop :=
  ∃ e : X ≃* ↥(Subgroup.closure (orthReflSet p m f)) ⧸
      Subgroup.center ↥(Subgroup.closure (orthReflSet p m f)),
    ∀ d ∈ D, ∃ r : ↥(Subgroup.closure (orthReflSet p m f)),
      (r : GL (Fin m) (ZMod p)) ∈ orthReflSet p m f ∧ e d = QuotientGroup.mk r

@[expose] def IsSevenNineGroup (X : Type) [Group X] (D : Set X) : Prop :=
  (∃ f : LinearMap.BilinForm (ZMod 5) (Fin 4 → ZMod 5), (∀ x y, f x y = f y x) ∧
      (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      (∀ a b : Fin 4 → ZMod 5, f a a = 0 → f a b = 0 → f b b = 0 →
        ∃ c d : ZMod 5, (c ≠ 0 ∨ d ≠ 0) ∧ c • a + d • b = 0) ∧
      IsReflModel 5 4 f X D) ∨
    (∃ f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3), (∀ x y, f x y = f y x) ∧
      (∀ x, (∀ y, f x y = 0) → x = 0) ∧ (IsReflModel 3 6 f X D ∨ IsReflQuotModel 3 6 f X D))

structure SevenNineConfig {X : Type} [Group X] (L S : Subgroup X) (p : ℕ) (Y Z : Subgroup X) :
    Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  card_s : Nat.card S = 2
  le : Y ≤ L
  elemAbelian : IsElemAbelian p Y
  s_le : S ≤ Subgroup.normalizer (Y : Set X)
  z_eq : Z = Y ⊓ Subgroup.centralizer (S : Set X)
  card_z : Nat.card Z * p = Nat.card Y
  z_le : Z ≤ ⨆ (g : X) (_ : g ∈ L) (_ : IsPGroup 2 ↥(S ⊔ conjSubgroup S g)), conjSubgroup S g
  exists_conj : ∀ B : Subgroup X, B ≤ Y → Nat.card B * p = Nat.card Y →
    ∃ h ∈ L, h ∈ Subgroup.normalizer (Y : Set X) ∧ conjSubgroup B h ≠ Z ∧
      ¬ ⁅Y, S⁆ ≤ conjSubgroup B h

@[expose] def OrthReflParabolic : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (L S : Subgroup X), S ≤ L → S ≠ ⊥ →
    IsSevenNineGroup ↥L {x : ↥L | (x : X) ∈ S ∧ x ≠ 1} →
    ∃ (p : ℕ) (Y Z : Subgroup X), SevenNineConfig L S p Y Z

variable {G : Type} [Group G]

@[expose] def commConjSup (V H E : Subgroup G) : Subgroup G :=
  ⨆ (k : G) (_ : k ∈ kSub V H E) (_ : ∀ a ∈ V, ∀ b ∈ conjSubgroup V k, a * b = b * a),
    conjSubgroup V k

structure SevenNineCompl (K J : Subgroup G) {X : Type} [Group X] (φ : ↥K →* X) (Yb : Subgroup X)
    (v : G) (P : Subgroup G) : Prop where
  le : P ≤ barPre K φ Yb
  inf_eq : P ⊓ (barPre K φ Yb ⊓ J) = ⊥
  sup_eq : P ⊔ (barPre K φ Yb ⊓ J) = barPre K φ Yb
  mem_normalizer : v ∈ Subgroup.normalizer (P : Set G)

end CFSG.LocalAnalysis.WeakClosure81

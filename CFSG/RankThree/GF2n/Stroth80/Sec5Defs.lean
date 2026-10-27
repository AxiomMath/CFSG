module

public import CFSG.RankThree.GF2n.Stroth80.Sec35

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure Sec5Hyp (hc : Ctx M Q Z B) (n : ℕ) (t : G) : Prop where
  width : Width Q Z n
  n_gt : 2 < n
  noA2 : NoA2 Q Z (LB M Q B)
  gen : GenByB M Q B
  mem : t ∈ LB M Q B
  notQ : t ∉ Q

omit [Finite G] in
@[expose] def Wt (Q V : Subgroup G) : Subgroup G := Q ⊓ Subgroup.centralizer (V : Set G)

@[expose] def Q1 (hc : Ctx M Q Z B) (t : G) : Subgroup G := CQtGrp hc (Subgroup.zpowers t)

omit [Finite G] in
@[expose] def Ut (Q Z : Subgroup G) (t : G) : Subgroup G := ⁅Q, Subgroup.zpowers t⁆ ⊔ Z

omit [Finite G] in
@[expose] def Tt (Q Z V : Subgroup G) (t : G) : Subgroup G :=
  ⁅Wt Q V, Subgroup.zpowers t⁆ ⊔ Z

omit [Finite G] in
@[expose] def IsChiIso (Q R K₀ U T₀ : Subgroup G) (t : G) : Prop :=
  (∀ x ∈ Q, ⁅x, t⁆ ∈ U) ∧ (∀ u ∈ U, ∃ x ∈ Q, ⁅x, t⁆ * u⁻¹ ∈ T₀) ∧
  (∀ x ∈ Q, ∀ y ∈ Q, ⁅x * y, t⁆ * (⁅x, t⁆ * ⁅y, t⁆)⁻¹ ∈ T₀) ∧
  (∀ x ∈ Q, (⁅x, t⁆ ∈ T₀ ↔ x ∈ K₀)) ∧
  (∀ r ∈ R, ∀ x ∈ Q, ⁅r * x * r⁻¹, t⁆ * (r * ⁅x, t⁆ * r⁻¹)⁻¹ ∈ T₀)

omit [Finite G] in
@[expose] def IsOppDecomp (P I L₁ L₂ A₁ A₂ : Subgroup G) : Prop :=
  I ≤ A₁ ∧ A₁ ≤ P ∧ I ≤ A₂ ∧ A₂ ≤ P ∧ A₁ ⊔ A₂ = P ∧ A₁ ⊓ A₂ = I ∧
  (∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ I) ∧ (∀ x ∈ P, x ^ 2 ∈ I) ∧
  (∀ x ∈ P, (x ∈ A₁ ↔ ∀ l ∈ L₁, ⁅l, x⁆ ∈ I)) ∧ (∀ x ∈ P, (x ∈ A₂ ↔ ∀ l ∈ L₂, ⁅l, x⁆ ∈ I))

omit [Finite G] in
@[expose] def IsIndecSec (R P I : Subgroup G) : Prop :=
  ¬ ∃ A₁ A₂ : Subgroup G, I ≤ A₁ ∧ A₁ ≤ P ∧ I ≤ A₂ ∧ A₂ ≤ P ∧ A₁ ≠ I ∧ A₂ ≠ I ∧
    A₁ ⊔ A₂ = P ∧ A₁ ⊓ A₂ = I ∧
    ∀ r ∈ R, conjSubgroup r A₁ = A₁ ∧ conjSubgroup r A₂ = A₂

omit [Finite G] in
@[expose] def HypPlane (Q Z B C : Subgroup G) (t : G) : Prop :=
  ∃ ĉ ∈ Q, ⁅ĉ, t⁆ ∈ C ⊔ Z ∧ ∃ b ∈ B, ⁅b, ĉ⁆ ≠ 1

@[expose] def SpNat (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧ ∃ m : ℕ, 2 ≤ m ∧
    NaturalRep (ι := Fin m ⊕ Fin m) K (StatedSp m K) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t)

@[expose] def OmegaNat (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧
    ((∃ m : ℕ, 3 ≤ m ∧ NaturalRep (ι := Fin m ⊕ Fin m) K
        (StatedOmega (StatedQuadPlus m K)) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
        (hc.CN t)) ∨
      (∃ (m : ℕ) (b c : K), 2 ≤ m ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        NaturalRep (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus m K b c)) (Rt M (LB M Q B) t)
          (Vt M (LB M Q B) B Z t) Z (hc.CN t)))

@[expose] def SLNat (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = Nat.card Z ∧ ∃ m : ℕ, 2 ≤ m ∧
    NaturalRep (ι := Fin m) K (StatedSL m K) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
      (hc.CN t)

end CFSG.RankThree.GF2n.Stroth80

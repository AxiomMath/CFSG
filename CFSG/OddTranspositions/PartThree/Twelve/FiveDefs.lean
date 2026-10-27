module

public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.PartFour.LinePolar
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.OddTranspositions.PartFour.LineStabilizer
public import CFSG.Permutation.BurnsideSchur

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

structure FiveChart (hC : HypothesisC D) (n : ℕ) where
  b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)
  hsym : ∀ x y, b x y = b y x
  hnd : ∀ x, (∀ y, b x y = 0) → x = 0
  vec : G → (Fin n → ZMod 5)
  norm_vec : ∀ z ∈ commSet D hC.d, b (vec z) (vec z) = 1
  exists_vec : ∀ v, b v v = 1 → ∃ z ∈ commSet D hC.d, vec z = v ∨ vec z = -v
  eq_of_vec : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d,
    vec z' = vec z ∨ vec z' = -vec z → z' = z
  commute_iff : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
    (Commute z z' ↔ b (vec z) (vec z') = 0)
  orderOf_mul : ∀ z ∈ commSet D hC.d, ∀ z' ∈ commSet D hC.d, z ≠ z' →
    b (vec z) (vec z') ≠ 0 → orderOf (z * z') = if b (vec z) (vec z') ^ 2 = 1 then 5 else 3
  vec_conj : ∀ x ∈ commSet D hC.d, ∀ y ∈ commSet D hC.d,
    vec (x * y * x⁻¹) = vec y - (2 * b (vec y) (vec x)) • vec x ∨
      vec (x * y * x⁻¹) = -(vec y - (2 * b (vec y) (vec x)) • vec x)

@[expose] def FiveLines (D : Set G) : Prop :=
  ∀ v ∈ D, ∀ a ∈ commSet D v, ∀ b ∈ commSet D v, ¬ Commute a b →
    (orderOf (a * b) = 3 ∨ orderOf (a * b) = 5) ∧ (lineMem D a b).ncard = orderOf (a * b) ∧
      ∀ c ∈ lineMem D a b, c ≠ a → ¬ Commute c a ∧ lineMem D a c = lineMem D a b

@[expose] def IsFiveHyperplane {hC : HypothesisC D} {n : ℕ} (c : FiveChart hC n) (w : G)
    (z : Fin n → ZMod 5) : Prop :=
  z ≠ 0 ∧ (if orderOf (hC.d * w) = 5 then c.b z z = 0 else c.b z z = 2) ∧
    ∀ y ∈ commSet D hC.d, (Commute y w ↔ c.b (c.vec y) z = 0)

end CFSG.OddTranspositions.PartThree

end

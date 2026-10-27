module

public import CFSG.LocalAnalysis.ZStar.BrauerBlockLift

public section

namespace CFSG

namespace ZStar.BrauerCoefficientFormula

open ZStar.Helpers

universe u

noncomputable section

variable {G : Type u} [Group G] [Fintype G]

noncomputable local instance subgroupFintype (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

@[expose] def TwoRegular {X : Type*} [Group X] (x : X) : Prop :=
  Odd (orderOf x)

@[expose] def TwoElement {X : Type*} [Group X] (x : X) : Prop :=
  Nat.isPowerOfTwo (orderOf x)

@[expose] noncomputable def principalPairWeight {X : Type*} [Group X]
    (x u : X) : ZMod 2 := by
  classical
  exact if TwoElement u ∧ TwoRegular (u⁻¹ * x) then 1 else 0

@[expose] noncomputable def principalCoefficientCount
    (X : Type*) [Group X] [Fintype X] (x : X) : ZMod 2 :=
  ∑ u : X, principalPairWeight x u

theorem orderOf_conj_eq (x y : G) :
    orderOf (x * y * x⁻¹) = orderOf y := by
  have hsemi : SemiconjBy x y (x * y * x⁻¹) := by
    show x * y = (x * y * x⁻¹) * x
    group
  exact (SemiconjBy.orderOf_eq x hsemi).symm

private theorem twoRegular_conj_iff (x y : G) :
    TwoRegular (x * y * x⁻¹) ↔ TwoRegular y := by
  rw [TwoRegular, TwoRegular, orderOf_conj_eq]

private theorem twoElement_conj_iff (x y : G) :
    TwoElement (x * y * x⁻¹) ↔ TwoElement y := by
  rw [TwoElement, TwoElement, orderOf_conj_eq]

private theorem principalPairWeight_conj
    (w x u : G) (hwx : w * x = x * w) :
    principalPairWeight x (w * u * w⁻¹) = principalPairWeight x u := by
  unfold principalPairWeight
  have hprod :
      (w * u * w⁻¹)⁻¹ * x = w * (u⁻¹ * x) * w⁻¹ := by
    calc
      (w * u * w⁻¹)⁻¹ * x = w * u⁻¹ * w⁻¹ * x := by group
      _ = w * u⁻¹ * (x * w⁻¹) := by
        have hwxi : w⁻¹ * x = x * w⁻¹ :=
          (Commute.inv_left (show Commute w x from hwx)).eq
        rw [mul_assoc, hwxi]
      _ = w * (u⁻¹ * x) * w⁻¹ := by group
  rw [twoElement_conj_iff, hprod, twoRegular_conj_iff]

private theorem principalCoefficientCount_eq_centralizer
    (w : G) (hw2 : w * w = 1)
    (x : Subgroup.centralizer ({w} : Set G)) :
    principalCoefficientCount G (x : G) =
      principalCoefficientCount (Subgroup.centralizer ({w} : Set G)) x := by
  rw [principalCoefficientCount, principalCoefficientCount]
  let F : G → ZMod 2 := fun u => principalPairWeight (x : G) u
  have hwx : w * (x : G) = (x : G) * w := by
    exact (Subgroup.mem_centralizer_singleton_iff.mp x.property).symm
  have hsum := ZStar.BrauerProjection.sum_eq_sum_centralizer_of_conjInvariant
    w hw2 F (fun u => principalPairWeight_conj w (x : G) u hwx)
  rw [hsum]
  apply Finset.sum_congr rfl
  intro u hu
  have hsing : TwoElement (u : G) ↔ TwoElement u := by
    unfold TwoElement
    rw [Subgroup.orderOf_coe]
  have hreg : TwoRegular ((u : G)⁻¹ * (x : G)) ↔
      TwoRegular (u⁻¹ * x) := by
    unfold TwoRegular
    change Odd (orderOf ((u⁻¹ * x :
      Subgroup.centralizer ({w} : Set G)) : G)) ↔ _
    rw [Subgroup.orderOf_coe]
  change principalPairWeight (x : G) (u : G) = principalPairWeight x u
  unfold principalPairWeight
  rw [hsing, hreg]

@[expose] noncomputable def HasPrincipalCoefficientFormula
    (X : Type*) [Group X] [Fintype X] : Prop := by
  classical
  exact ∀ x : X,
    (principalBlockCandidate X).coeff x =
      if TwoRegular x then principalCoefficientCount X x else 0

private theorem principalBlockCandidate_centralizer_coeff_eq_ambient
    (w : G) (hw2 : w * w = 1)
    (hformulaG : HasPrincipalCoefficientFormula G)
    (hformulaC : HasPrincipalCoefficientFormula
      (Subgroup.centralizer ({w} : Set G)))
    (x : Subgroup.centralizer ({w} : Set G)) :
    (principalBlockCandidate (Subgroup.centralizer ({w} : Set G))).coeff x =
      (principalBlockCandidate G).coeff (x : G) := by
  rw [hformulaC, hformulaG]
  have hregular : TwoRegular (x : G) ↔ TwoRegular x := by
    rw [TwoRegular, TwoRegular, Subgroup.orderOf_coe]
  by_cases hx : TwoRegular x
  · rw [ite_eq_left hx, ite_eq_left (hregular.mpr hx)]
    exact (principalCoefficientCount_eq_centralizer w hw2 x).symm
  · rw [ite_eq_right hx, ite_eq_right (fun h => hx (hregular.mp h))]

theorem principalBlockCandidate_ambientConjInvariant_of_formula
    (w : G) (hw2 : w * w = 1)
    (hformulaG : HasPrincipalCoefficientFormula G)
    (hformulaC : HasPrincipalCoefficientFormula
      (Subgroup.centralizer ({w} : Set G))) :
    ZStar.BrauerBlockLift.AmbientConjInvariant w
      (principalBlockCandidate (Subgroup.centralizer ({w} : Set G))) := by
  intro a b hab
  rw [principalBlockCandidate_centralizer_coeff_eq_ambient
      w hw2 hformulaG hformulaC a,
    principalBlockCandidate_centralizer_coeff_eq_ambient
      w hw2 hformulaG hformulaC b]
  have hcentral := principalBlockCandidate_central G
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  have hcoeff := congrArg
    (fun z : GroupAlgebraTwo G => z.coeff (g * (a : G)))
    (hcentral g)
  simpa [hg, MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, mul_assoc] using hcoeff

end

end ZStar.BrauerCoefficientFormula

end CFSG

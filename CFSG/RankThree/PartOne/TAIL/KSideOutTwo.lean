module

public import CFSG.RankThree.PartOne.TAIL.KSideAbs
public import CFSG.RankThree.PartOne.TAIL.KSideCen
public import CFSG.LocalAnalysis.ComponentInitial.LinearTwoOuterOrder
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven

public section

namespace CFSG.RankThree.PartOne.TAIL

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.GorensteinWalter (PSL2)

theorem OutData.of_outer {X : Type*} [Group X] (hcomm : ∀ a b : Outer X, a * b = b * a)
    (hcard : Nat.card (Outer X) ∣ 42) : OutData X := by
  refine ⟨fun a b => ?_, hcard⟩
  have h : (QuotientGroup.mk (a * b * a⁻¹ * b⁻¹) : Outer X) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hcomm (a : Outer X) b]
    group
  exact (QuotientGroup.eq_one_iff _).1 h

theorem outData_sl_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 21) :
    OutData (Matrix.SpecialLinearGroup (Fin 2) F) := by
  classical
  have := Fintype.ofFinite F
  have hFcard : Fintype.card F = 2 ^ 21 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hFcard
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ :=
    center_sl_eq_bot (by norm_num) (by rw [hF]; norm_num)
  let e1 : Matrix.SpecialLinearGroup (Fin 2) F ≃* PSL2 F :=
    (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hcen.symm)
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F ≃* coordinateG F :=
    e1.trans (pslEquivCoordinateG F)
  have hEG : IsCyclic (CoordinateQuotientEG F) := by
    have hDG : coordinateD F = coordinateG F :=
      CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.coordinateD_eq_G
    have e : CoordinateQuotientEG F ≃* CoordinateQuotientED F :=
      QuotientGroup.quotientMulEquivOfEq (by rw [hDG])
    exact e.isCyclic.2 (coordinateED_isCyclic F)
  have hcommG : ∀ a b : Outer (coordinateG F), a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := (coordinateOuterQuotientEquiv F).surjective a
    obtain ⟨b', rfl⟩ := (coordinateOuterQuotientEquiv F).surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    let _ : CommGroup (CoordinateQuotientEG F) := IsCyclic.commGroup
    exact mul_comm a' b'
  refine OutData.of_outer ?_ ?_
  · intro a b
    apply (CFSG.ComponentClassification.OuterAutomorphisms.equivalence ψ).injective
    rw [map_mul, map_mul]
    exact hcommG _ _
  · have h := (CFSG.LocalAnalysis.ComponentInitial.linear_two_outer_order_divisor (p := 2)
      (f := 21) Nat.prime_two F hF).2 (Matrix.SpecialLinearGroup (Fin 2) F) ⟨e1⟩
    exact h.trans (by norm_num)

end CFSG.RankThree.PartOne.TAIL

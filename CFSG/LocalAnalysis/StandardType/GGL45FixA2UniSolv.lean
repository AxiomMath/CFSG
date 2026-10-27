module

public import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputs
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcLTwoEight
public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSUInner
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial

theorem gffa2_unitary_solvable {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    Group.IsSolvable ↥(ggAutFixedSubgroup (psuField h σ)) := by
  have hfix : ggAutFixedSubgroup (psuField h σ) =
      (psuField h σ).toMonoidHom.eqLocus (MonoidHom.id (unitaryPSU h 3)) :=
    Subgroup.ext fun _ => Iff.rfl
  have hcard : Nat.card ↥(ggAutFixedSubgroup (psuField h σ)) = 2 ^ 3 * 3 ^ 3 := by
    rw [hfix, CFSG.RankThree.PartTwo.Sec8.Item812Res3.card_fixedPoints_psuField h hσ]
    norm_num
  haveI : Finite ↥(ggAutFixedSubgroup (psuField h σ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact ggIsSolvable_of_card_eq_pow_mul_pow (p := 2) (q := 3) (a := 3) (b := 3)
    Nat.prime_two Nat.prime_three (by norm_num) hcard

end CFSG.StandardType

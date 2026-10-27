module

public import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
import CFSG.RankThree.PartTwo.Census.Classical.EvenUnitary
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem pRank_quotient_center_le_three {X : Type*} [Group X] [Finite X]
    (h : ¬ 3 ^ 4 ∣ Nat.card X) : CFSG.pRank 3 (X ⧸ Subgroup.center X) ≤ 3 :=
  pRank_three_le_of_not_dvd fun h3 => h (h3.trans (Subgroup.index_dvd_card _))

theorem card_projSL_dvd (n : ℕ) (F : Type) [Field F] [Finite F] :
    Nat.card (projSL n F) ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) F) := by
  rw [Nat.card_congr (projSLEquivPSLn n F).toEquiv]
  exact Subgroup.index_dvd_card _

theorem card_projSU_dvd (n p f : ℕ) [Fact p.Prime] [Finite (CFSG.Assembly.LowTwoRank.StatedSU n
      (p ^ f) (GaloisField p (2 * f)))] :
    Nat.card (projSU n p f) ∣
      Nat.card (CFSG.Assembly.LowTwoRank.StatedSU n (p ^ f) (GaloisField p (2 * f))) := by
  rw [Nat.card_congr (projSUEquivStatedProj n p f).toEquiv]
  exact Subgroup.index_dvd_card _

theorem pRank_projSL_three_three :
    CFSG.pRank 3 (projSL 3 (GaloisField 3 1) ⧸ Subgroup.center (projSL 3 (GaloisField 3 1))) ≤
      3 := by
  have : Finite (projSL 3 (GaloisField 3 1)) :=
    Finite.of_equiv _ (projSLEquivPSLn 3 (GaloisField 3 1)).symm.toEquiv
  refine pRank_quotient_center_le_three fun h => ?_
  have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have h1 := h.trans (card_projSL_dvd 3 (GaloisField 3 1))
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 3 1 (by norm_num)] at h1
  norm_num [Fin.prod_univ_succ] at h1

theorem pRank_projSL_five_two :
    CFSG.pRank 3 (projSL 5 (GaloisField 2 1) ⧸ Subgroup.center (projSL 5 (GaloisField 2 1))) ≤
      3 := by
  have : Finite (projSL 5 (GaloisField 2 1)) :=
    Finite.of_equiv _ (projSLEquivPSLn 5 (GaloisField 2 1)).symm.toEquiv
  refine pRank_quotient_center_le_three fun h => ?_
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h1 := h.trans (card_projSL_dvd 5 (GaloisField 2 1))
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, GaloisField.card 2 1 (by norm_num)] at h1
  norm_num [Fin.prod_univ_succ] at h1

theorem pRank_projSU_three_three :
    CFSG.pRank 3 (projSU 3 3 1 ⧸ Subgroup.center (projSU 3 3 1)) ≤ 3 := by
  have hK : Nat.card (GaloisField 3 (2 * 1)) = 9 := by
    rw [card_galoisField 3 (2 * 1) (by norm_num)]
    norm_num
  have hSU : Nat.card (CFSG.Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1))) =
      6048 := by simpa using CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU hK
  have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) (GaloisField 3 (2 * 1))) :=
    Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
  have : Finite (projSU 3 3 1) := Finite.of_equiv _ (projSUEquivStatedProj 3 3 1).symm.toEquiv
  refine pRank_quotient_center_le_three fun h => ?_
  have h1 := h.trans (card_projSU_dvd 3 3 1)
  rw [hSU] at h1
  norm_num at h1

theorem pRank_projSU_five_four :
    CFSG.pRank 3 (projSU 5 2 2 ⧸ Subgroup.center (projSU 5 2 2)) ≤ 3 := by
  have hU := unitaryFieldData_galoisField 2 2 (by norm_num)
  have hSU := CFSG.RankThree.PartTwo.Census.card_statedSU_five_four hU
  have : Finite (CFSG.Assembly.LowTwoRank.StatedSU 5 (2 ^ 2) (GaloisField 2 (2 * 2))) :=
    Nat.finite_of_card_ne_zero (by rw [hSU]; norm_num)
  have : Finite (projSU 5 2 2) := Finite.of_equiv _ (projSUEquivStatedProj 5 2 2).symm.toEquiv
  refine pRank_quotient_center_le_three fun h => ?_
  have h1 := h.trans (card_projSU_dvd 5 2 2)
  rw [hSU] at h1
  norm_num at h1

theorem rankEight_holds :
    CFSG.pRank 3 (projSL 3 (GaloisField 3 1) ⧸
        Subgroup.center (projSL 3 (GaloisField 3 1))) ≤ 3 ∧
      CFSG.pRank 3 (projSU 3 3 1 ⧸ Subgroup.center (projSU 3 3 1)) ≤ 3 :=
  ⟨pRank_projSL_three_three, pRank_projSU_three_three⟩

theorem rankSeven_of_Sp62
    (h : CFSG.pRank 3 (projSp 3 (GaloisField 2 1) ⧸
      Subgroup.center (projSp 3 (GaloisField 2 1))) ≤ 3) :
    CFSG.pRank 3 (projSL 5 (GaloisField 2 1) ⧸
        Subgroup.center (projSL 5 (GaloisField 2 1))) ≤ 3 ∧
      CFSG.pRank 3 (projSp 3 (GaloisField 2 1) ⧸
        Subgroup.center (projSp 3 (GaloisField 2 1))) ≤ 3 ∧
      CFSG.pRank 3 (projSU 5 2 2 ⧸ Subgroup.center (projSU 5 2 2)) ≤ 3 :=
  ⟨pRank_projSL_five_two, h, pRank_projSU_five_four⟩

end CFSG.RankThree.PartTwo.Sec4

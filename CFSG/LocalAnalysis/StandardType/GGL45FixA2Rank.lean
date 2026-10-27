module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.RankThree.PartTwo.Sec4.Item413AutL3
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem gffa2_rank_linear {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))))
    (hA : IsElemAbelian 3 A) : Nat.card A ≤ 3 ^ 3 := by
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card Nat.prime_two (by norm_num) hK
  have hcard := card_le_of_mulEquiv_mulAut (TypeA.recipeEquiv 3 K)
    (fun B hB => card_le_27_of_mulAut_projectiveSL_three h3 B hB) A hA
  rwa [show (27 : ℕ) = 3 ^ 3 by norm_num] at hcard

theorem gffa2_rank_unitary {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2)
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))))
    (hA : IsElemAbelian 3 A) : Nat.card A ≤ 3 ^ 3 := by
  have hn1 : 1 ≤ n := by omega
  have h : UnitaryFieldData 2 n K := unitaryFieldData_of_card hn1 hK
  have hK' : Nat.card K = 2 ^ (2 * n) := by
    rw [hK, mul_comm 2 n, pow_mul]
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card Nat.prime_two (by norm_num) hK'
  have hq : 2 < 2 ^ n := by
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num]
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mpr (by omega)
  have hcard := card_le_of_mulEquiv_mulAut (unitaryPSUEquiv h (by norm_num : 1 ≤ 3)).symm
    (fun B hB => card_le_27_of_mulAut_unitaryPSU (h := h) h3 hq B hB) A hA
  rwa [show (27 : ℕ) = 3 ^ 3 by norm_num] at hcard

end CFSG.StandardType

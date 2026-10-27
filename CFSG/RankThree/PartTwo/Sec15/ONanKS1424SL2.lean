module

import CFSG.RankThree.PartOne.KLAY.Core
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Steinberg.CentralExt.SUTwo
public import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA

public section

namespace CFSG.RankThree.PartTwo.Sec15.KS1424

open CFSG CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

variable {K : Type} [Field K] {π : Bool} {n : ℕ}

open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg in
theorem sl2_data (hK : PiField π 2 n K) (hn : 2 ≤ n) :
    IsSimpleGroup ↥(slPi π 2 (2 ^ n) K) ∧
      Nat.card ↥(slPi π 2 (2 ^ n) K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have := hK.finite
  have := hK.charP
  cases π
  · have hcard : Nat.card K = (2 ^ n) ^ 2 := hK.card
    obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hcard
    obtain ⟨P, hP⟩ := exists_wittMatrix hcard 2
    have e : SL(2, fixedSubfield K 2 n) ≃* StatedSU 2 (2 ^ n) K :=
      ((hypEquiv hζ0 hζ).trans (conjEquiv P hP)).trans
        (MulEquiv.subgroupCongr (SUid_eq_statedSU hcard 2))
    have hF : Nat.card (fixedSubfield K 2 n) = 2 ^ n := card_fixedSubfield hcard
    have h4 : 4 ≤ Nat.card (fixedSubfield K 2 n) := by
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : CharP (fixedSubfield K 2 n) 2 := inferInstance
    have := CFSG.RankThree.PartOne.KLAY.isSimpleGroup_SL_two h4
    refine ⟨e.symm.isSimpleGroup, ?_⟩
    change Nat.card ↥(StatedSU 2 (2 ^ n) K) = _
    rw [← Nat.card_congr e.toEquiv, card_specialLinearGroup_fin_two, hF]
  · have hcard : Nat.card K = 2 ^ n := hK.card
    have h4 : 4 ≤ Nat.card K := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    let e : SL(2, K) ≃* ↥(slPi true 2 (2 ^ n) K) :=
      (MonoidHom.ofInjective (G := SL(2, K)) (N := GL (Fin 2) K)
        (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective).trans
        (MulEquiv.subgroupCongr (statedSL_eq_range_toGL 2 K).symm)
    have := CFSG.RankThree.PartOne.KLAY.isSimpleGroup_SL_two h4
    refine ⟨e.symm.isSimpleGroup, ?_⟩
    rw [← Nat.card_congr e.toEquiv, card_specialLinearGroup_fin_two, hcard]

end CFSG.RankThree.PartTwo.Sec15.KS1424

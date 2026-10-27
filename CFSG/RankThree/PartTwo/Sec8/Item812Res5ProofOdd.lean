module

import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.Permutation.UnitaryThreeRecognition.ModelFinite
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

namespace Item812Res5

theorem padicValNat_card_projSL_three {g : ℕ} (hg : 1 ≤ g) :
    padicValNat 2 (Nat.card (projSL 3 (GaloisField 2 g))) = 3 * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := KFacts.KS14.card_projSL_three_mul_gcd (GaloisField 2 g)
  rw [GaloisField.card 2 g (by omega)] at h
  set c := Nat.card (projSL 3 (GaloisField 2 g)) with hc
  set q := 2 ^ g with hq
  have hc0 : c ≠ 0 := Nat.card_pos.ne'
  have hd3 : Nat.gcd 3 (q - 1) ∣ 3 := Nat.gcd_dvd_left _ _
  have hd0 : Nat.gcd 3 (q - 1) ≠ 0 := Nat.gcd_ne_zero_left (by norm_num)
  have hd2 : ¬ 2 ∣ Nat.gcd 3 (q - 1) := fun h2 => by
    have h23 := h2.trans hd3
    omega
  have hq2 : 2 ∣ q := dvd_pow_self 2 (by omega)
  have hqa : 2 ∣ q ^ 2 := dvd_pow hq2 (by norm_num)
  have hqb : 2 ∣ q ^ 3 := dvd_pow hq2 (by norm_num)
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hqa1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hqb1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ hq1
  have hR2 : ¬ 2 ∣ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    rw [Nat.Prime.dvd_mul Nat.prime_two]
    omega
  have hR0 : (q ^ 2 - 1) * (q ^ 3 - 1) ≠ 0 := fun h0 => hR2 (h0 ▸ dvd_zero 2)
  have hq0 : q ≠ 0 := by omega
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul hc0 hd0, padicValNat.eq_zero_of_not_dvd hd2, add_zero,
    padicValNat.mul (pow_ne_zero 3 hq0) hR0, padicValNat.eq_zero_of_not_dvd hR2, add_zero,
    padicValNat.pow q 3, hq, padicValNat.prime_pow] at h1
  exact h1

end Item812Res5

open Item812Res5

end CFSG.RankThree.PartTwo.Sec8

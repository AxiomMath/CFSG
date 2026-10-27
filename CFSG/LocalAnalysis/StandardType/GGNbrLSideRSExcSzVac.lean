module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideRSExcVac
import CFSG.LieType.Ree.SuzukiOrder
import CFSG.HardMathSupport.Solomon.Coordinator.L3BDeltaOuter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem asz_not_three_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq3 : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hq1' : (2 ^ (2 * a + 1) - 1) % 3 = 1 := by omega
  have hsq : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq3]
  have hsq1 : ((2 ^ (2 * a + 1)) ^ 2 + 1) % 3 = 2 := by omega
  have h1 : (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) % 3 = 1 := by
    rw [Nat.mul_mod, hsq, hq1']
  have h2 : (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) % 3 = 2 := by
    rw [Nat.mul_mod, h1, hsq1]
  omega

theorem ggNbrLSideNoPSL3_twB2 {a : ℕ} {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    GGNbrLSideNoPSL3 (LargeEvenInnSet (LargeEvenCenterQuot (LargeEvenSzGroup a K))) := by
  intro φ _ _ _ J _ F _ _ _
  refine ⟨fun e => ?_⟩
  haveI : Finite ↥(LargeEvenSzGroup a K) := Subtype.finite
  haveI : Finite (LargeEvenCenterQuot (LargeEvenSzGroup a K)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  have hnotSz : ¬ 3 ∣ Nat.card ↥(LargeEvenSzGroup a K) := by
    rw [largeEvenSzGroup_eq a K, CFSG.LieType.Ree.suzuki_order (a := a) (K := K) hK]
    exact asz_not_three_dvd_suzuki_order a
  have h3 : 3 ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.HardMathSupport.Solomon.Coordinator.three_dvd_card_projectiveSL F
  exact hnotSz (h3.trans ((Subgroup.card_quotient_dvd_card (Subgroup.center ↥J)).trans
    ((Subgroup.card_subgroup_dvd_card J).trans
      (Subgroup.card_quotient_dvd_card (Subgroup.center ↥(LargeEvenSzGroup a K))))))

end CFSG.StandardType

end

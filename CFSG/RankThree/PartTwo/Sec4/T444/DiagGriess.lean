module

public import CFSG.RankThree.PartTwo.Sec4.Item41NarrowGriess
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ProvedRows
public import CFSG.RankThree.PartTwo.Sec4.T444.DiagFinalDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.TBLit (griessMultipliersAllModels_holds)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator (card_hopfMultiplier_eq_of_mulEquiv)

theorem diag_item41LargePrime_holds
    : Item4_1LargePrime :=
  CFSG.RankThree.PartTwo.Sec4.Item41Narrow.item4_1LargePrime_of_griess
    griessMultipliersAllModels_holds

theorem diag_item43_holds
    : Item4_3 :=
  CFSG.RankThree.PartTwo.Sec4.Census.rank3II_4_3_of_griess_noItem41 griessMultipliersAllModels_holds

theorem diag_coverCenterThree_holds
    : CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThree :=
  CFSG.RankThree.PartTwo.Sec4.Census.coverCenterThree_of_rest
    (CFSG.RankThree.PartTwo.Sec4.Census.coverCenterThreeRest_of griessMultipliersAllModels_holds)

theorem diagGriess_lieModel_projSL {m : ℕ} (hm : 2 ≤ m) :
    CFSG.Models.LieModel (projSL 3 (GaloisField 2 (2 * m))) .PSL 3 2 (2 * m) := by
  have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 3 2 (2 * m) :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩
  refine ⟨hadm, Or.inl ⟨hadm, GaloisField 2 (2 * m), inferInstance, inferInstance, ?_,
    ⟨CFSG.RankThree.PartTwo.KFacts.KS44.projSLEquivStatedProj (GaloisField 2 (2 * m))⟩⟩⟩
  exact GaloisField.card 2 (2 * m) (by omega)

theorem diagGriess_card_mult_sl3 {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 3 2 (2 * m) ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 (2 * m)) = 3 := by
  have h4 : 2 ^ (2 * m) = 4 ^ m := by
    norm_num [pow_mul]
  have hmod : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h3 : 3 ∣ 2 ^ (2 * m) - 1 := by
    rw [h4]
    omega
  have hgen : CFSG.Blueprint.Multiplier.genericOrders .PSL 3 2 (2 * m) = (3, 1) := by
    change (Nat.gcd 3 (2 ^ (2 * m) - 1), 1) = (3, 1)
    rw [Nat.gcd_eq_left h3]
  have hexc : CFSG.Blueprint.Multiplier.exceptionalOrders .PSL 3 2 (2 * m) = (1, 1) := by
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> first | rfl | (exfalso; omega) | simp_all | omega
  have hmul : ∀ α : Type, Nat.card (Multiplicative α) = Nat.card α :=
    fun α => Nat.card_congr Multiplicative.toAdd
  unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  norm_num [Nat.card_prod, hmul, Nat.card_zmod]

theorem diagGriess_card_projSL
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {m : ℕ} (hm : 2 ≤ m) :
    Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (projSL 3 (GaloisField 2 (2 * m)))) = 3 := by
  obtain ⟨-, ⟨e⟩⟩ := hGA _ .PSL 3 2 (2 * m) (diagGriess_lieModel_projSL hm)
  rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      (projSL 3 (GaloisField 2 (2 * m)))).toEquiv,
    Nat.card_congr e.toEquiv, diagGriess_card_mult_sl3 hm]

theorem diagGriess_centerPrimeTwo_of_card_dvd (T : Type) [Group T]
    (hT : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier T) ∣ 48) :
    CenterThreePrimeTwoAt T := by
  intro X _ _ hX hψ Z hZ h3
  obtain ⟨ψ⟩ := hψ
  have h := CFSG.RankThree.PartTwo.KFacts.KS44.card_center_dvd_card_hopfMultiplier hX
  rw [card_hopfMultiplier_eq_of_mulEquiv ψ] at h
  exact CFSG.RankThree.PartTwo.KFacts.KS44.isPGroup_two_of_le_center (h.trans hT) hZ h3

theorem diag_centerSL3_holds
    : ∀ m : ℕ, 2 ≤ m → CenterThreePrimeTwoAt (projSL 3 (GaloisField 2 (2 * m))) := by
  intro m hm
  apply diagGriess_centerPrimeTwo_of_card_dvd
  rw [diagGriess_card_projSL griessMultipliersAllModels_holds hm]
  norm_num

theorem diag_centerM22_holds
    : CenterThreePrimeTwoAt Blueprint.NativeSporadic.M22 := by
  apply diagGriess_centerPrimeTwo_of_card_dvd
  have h : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (Blueprint.NativeSporadic.M22)) = 12 :=
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.nativeRow_M22
  rw [h]
  norm_num

end CFSG.RankThree.PartTwo.Sec4

module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2TwAModel
public import CFSG.Blueprint.MultiplierDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessSchurMultipliersMilestoneDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (IsSU5)

private theorem exceptionalOrders_psu5 (m : ℕ) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 5 2 m = (1, 1) := by
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem card_center_dvd_of_isSU5
    {X : Type} [Group X] [Finite X] {m : ℕ} (h : IsSU5 X m) :
    Nat.card (Subgroup.center X) ∣ Nat.gcd 5 (2 ^ m + 1) := by
  obtain ⟨hQ, hM⟩ := h
  have hM' : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU (4 + 1) 2 m := hM
  have hQ' : CFSG.IsQuasisimple X := hQ
  have hcard := CFSG.LocalAnalysis.GLTheoremA.rk2_card_griess_twA hM' (exceptionalOrders_psu5 m)
  have hgpos : Nat.gcd (4 + 1) (2 ^ m + 1) ≠ 0 := (Nat.gcd_pos_of_pos_right _ (by positivity)).ne'
  have : Finite (CFSG.Open.griessHopfMultiplier (X ⧸ Subgroup.center X)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hgpos)
  have h1 := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_center_dvd_hopf hQ' (MulEquiv.refl _)
  rwa [hcard] at h1

theorem not_three_dvd_card_center_of_isSU5
    {X : Type} [Group X] [Finite X] {m : ℕ} (h : IsSU5 X m) :
    ¬ 3 ∣ Nat.card (Subgroup.center X) := fun h3 =>
  absurd (h3.trans ((card_center_dvd_of_isSU5 h).trans (Nat.gcd_dvd_left 5 _))) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

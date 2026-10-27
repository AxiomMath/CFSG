module

public import CFSG.RankThree.PartOne.KF.U4Final
public import CFSG.RankThree.PerfectCover.HopfFormula
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover

theorem card_multiplier_psu_four_even {f : ℕ} (hf : 2 ≤ f) :
    Nat.card (Blueprint.Multiplier.generic .PSU 4 2 f ×
      Blueprint.Multiplier.exceptional .PSU 4 2 f) = 1 := by
  have hcop : Nat.Coprime 4 (2 ^ f + 1) := by
    have h2 : Nat.Coprime 2 (2 ^ f + 1) := by
      rw [Nat.coprime_two_left]
      exact (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
    simpa using Nat.Coprime.pow_left 2 h2
  have hgen : Blueprint.Multiplier.genericOrders .PSU 4 2 f = (1, 1) := by
    change (Nat.gcd 4 (2 ^ f + 1), 1) = (1, 1)
    rw [hcop]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 4 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem psuFourEvenCenterTrivial_of_multipliers
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    PSUFourEvenCenterTrivial := by
  intro X _ _ f hf hqs hmodel
  have hm : Models.LieModel (X ⧸ Subgroup.center X) .PSU 4 2 f := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSU 4 2 f hm
  have : Group.IsPerfect (X ⧸ Subgroup.center X) := ⟨hcomm⟩
  have : Group.IsPerfect X := hqs.1
  have hker : (QuotientGroup.mk' (Subgroup.center X)).ker ≤ Subgroup.center X :=
    (QuotientGroup.ker_mk' _).le
  obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
    perfect_central_kernel_quotient_of_schur_multiplier (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective _) hker
  have hdvd : Nat.card (QuotientGroup.mk' (Subgroup.center X)).ker ∣
      Nat.card (hopfMultiplier (X ⧸ Subgroup.center X)) := by
    rw [← Nat.card_congr e'.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rw [Nat.card_congr (hopfMultiplierEquivGriess _).symm.toEquiv, Nat.card_congr e.toEquiv,
    card_multiplier_psu_four_even hf, Nat.dvd_one, QuotientGroup.ker_mk'] at hdvd
  rw [← Subgroup.card_eq_one]
  exact hdvd

theorem kf126U4_of_multipliers
    (hGA : CFSG.Open.GriessAllModelsStatement) : KF126U4 :=
  kf126U4_of_inputs (psuFourEvenCenterTrivial_of_multipliers hGA)

end CFSG.RankThree.PartOne

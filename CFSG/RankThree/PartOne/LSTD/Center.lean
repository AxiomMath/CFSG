module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.PartOne.LSTD

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne

theorem card_multiplier_psu_five {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) :
    Nat.card (Blueprint.Multiplier.generic .PSU 5 2 f ×
      Blueprint.Multiplier.exceptional .PSU 5 2 f) = 5 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSU 5 2 f = (5, 1) := by
    change (Nat.gcd 5 (2 ^ f + 1), 1) = (5, 1)
    rw [Nat.gcd_eq_left h5]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 5 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem psuFive_center_trivial
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) (hperf : Group.IsPerfect X)
    (hZ : ¬ 5 ∣ Nat.card (Subgroup.center X))
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 5 2 f) :
    Subgroup.center X = ⊥ := by
  have hm : Models.LieModel (X ⧸ Subgroup.center X) .PSU 5 2 f := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSU 5 2 f hm
  have : Group.IsPerfect (X ⧸ Subgroup.center X) := ⟨hcomm⟩
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
    card_multiplier_psu_five h5, QuotientGroup.ker_mk'] at hdvd
  have hcop : Nat.Coprime (Nat.card (Subgroup.center X)) 5 :=
    (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hZ))
  rw [← Subgroup.card_eq_one]
  exact (Nat.Coprime.eq_one_of_dvd hcop hdvd)

end CFSG.RankThree.PartOne.LSTD

module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.RankThree.PartOne

theorem coprime_three_two_pow_add_one {f : ℕ} (hf : Even f) : Nat.Coprime 3 (2 ^ f + 1) := by
  obtain ⟨m, rfl⟩ := hf
  have h : (2 ^ (m + m) + 1) % 3 = 2 := by
    rw [← two_mul, pow_mul, Nat.add_mod, Nat.pow_mod]
    norm_num
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  omega

theorem card_multiplier_psu_three_even {f : ℕ} (hf : Even f) :
    Nat.card (Blueprint.Multiplier.generic .PSU 3 2 f ×
      Blueprint.Multiplier.exceptional .PSU 3 2 f) = 1 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSU 3 2 f = (1, 1) := by
    change (Nat.gcd 3 (2 ^ f + 1), 1) = (1, 1)
    rw [coprime_three_two_pow_add_one hf]
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSU 3 2 f = (1, 1) := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem psuThree_center_trivial
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {f : ℕ} (hfe : Even f) (hperf : Group.IsPerfect X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 f) :
    Subgroup.center X = ⊥ := by
  have hm : Models.LieModel (X ⧸ Subgroup.center X) .PSU 3 2 f := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hcomm, ⟨e⟩⟩ := hGA _ .PSU 3 2 f hm
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
    card_multiplier_psu_three_even hfe, Nat.dvd_one, QuotientGroup.ker_mk'] at hdvd
  rw [← Subgroup.card_eq_one]
  exact hdvd

end CFSG.RankThree.PartOne.CTP

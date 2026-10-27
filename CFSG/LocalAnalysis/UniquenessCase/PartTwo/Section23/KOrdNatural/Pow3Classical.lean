module

public import CFSG.Open.StatedDefs
import CFSG.Open.StatedAPI
import CFSG.ClassicalInvolution.Asc77.AscSCH19
import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
import CFSG.ClassicalInvolution.Asc77.AscSCH03
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.RankThree.CentralLift.ClassicalScalarCover
import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

open CFSG.Open

variable {K : Type} [Field K] [Finite K]

theorem pow_three_dvd_card_statedSL_three : Nat.card K ^ 3 ∣ Nat.card ↥(StatedSL 3 K) := by
  rw [CFSG.Open.StatedAPI.card_statedSL_three]
  exact dvd_mul_right _ _

theorem pow_three_dvd_card_statedSL_four : Nat.card K ^ 3 ∣ Nat.card ↥(StatedSL 4 K) := by
  rw [CFSG.ClassicalInvolution.Asc77.SCH.card_statedSL_four]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right
    (pow_dvd_pow (Nat.card K) (by norm_num : 3 ≤ 6)) _) _) _

theorem pow_three_dvd_card_statedSp_two : Nat.card K ^ 3 ∣ Nat.card ↥(StatedSp 2 K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp_two]
  exact Dvd.dvd.mul_right (pow_dvd_pow (Nat.card K) (by norm_num : 3 ≤ 4)) _

theorem pow_three_dvd_card_statedSp_three : Nat.card K ^ 3 ∣ Nat.card ↥(StatedSp 3 K) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 3]
  exact Dvd.dvd.mul_right (pow_dvd_pow (Nat.card K) (by norm_num : 3 ≤ 3 ^ 2)) _

theorem pow_three_dvd_card_statedSU_four {a : ℕ} (hK : Nat.card K = (2 ^ a) ^ 2) :
    Nat.card K ^ 3 ∣ Nat.card ↥(StatedSU 4 (2 ^ a) K) := by
  have hcard : 1 < Nat.card K := by
    haveI := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst a
      rw [hK] at hcard
      norm_num at hcard
    · exact h
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 a K :=
    ⟨Nat.prime_two, ha, by rw [hK, ← pow_mul, mul_comm]⟩
  have hK3 : Nat.card K ^ 3 = (2 ^ a) ^ 6 := by rw [hK, ← pow_mul]
  rw [hK3, CFSG.ClassicalInvolution.Asc77.SCH.card_statedSU_four hdata]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _) _

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOrdNat

end

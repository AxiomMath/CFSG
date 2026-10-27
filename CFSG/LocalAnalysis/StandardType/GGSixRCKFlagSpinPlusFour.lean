module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagSpinPlusFourAux

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal

theorem rckFlagSC4_oddCenter_quadPlus_two (g : ℕ) (_hg : 1 ≤ g) :
    OddCenterOf (Spin.spinMatrix (Spin.quadPlus 2 (GaloisField 2 g))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : GaloisField 2 g) = 0 := CharP.cast_eq_zero (GaloisField 2 g) 2
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus 2 (GaloisField 2 g))) :=
    (MonoidHom.ker_eq_bot_iff _).1 (Spin.ker_spinMatrix_quadPlus_eq_bot h2)
  haveI : Finite (spinGroup (Spin.quadPlus 2 (GaloisField 2 g))) :=
    Finite.of_injective _ hinj
  unfold OddCenterOf
  rw [← Nat.not_even_iff_odd]
  intro heven
  have : Fintype (Subgroup.center (spinGroup (Spin.quadPlus 2 (GaloisField 2 g)))) :=
    Fintype.ofFinite _
  have h2dvd : 2 ∣ Fintype.card
      (Subgroup.center (spinGroup (Spin.quadPlus 2 (GaloisField 2 g)))) := by
    rw [← Nat.card_eq_fintype_card]
    exact even_iff_two_dvd.mp heven
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card 2 h2dvd
  have hzsq : z * z = 1 := by
    have h : z ^ orderOf z = 1 := pow_orderOf_eq_one z
    rw [hzord, pow_two] at h
    exact h
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hzU : (z : spinGroup (Spin.quadPlus 2 (GaloisField 2 g))) *
      (z : spinGroup (Spin.quadPlus 2 (GaloisField 2 g))) = 1 := by
    simpa using congrArg Subtype.val hzsq
  exact hz1 (Subtype.ext (rckSP4_central_sq_eq_one h2 z z.2 hzU))

theorem rckFlagSpinPlusFourOdd_holds : RCKFlagSpinPlusFourOdd := fun g hg =>
  rckFlagSC4_oddCenter_quadPlus_two g hg

end CFSG.StandardType.RCKFlag

module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Main
public import CFSG.Milestones.ASVolI.A3Spor.Out
public import CFSG.Milestones.ASVolI.A3OddFacts
public import CFSG.Milestones.CAT_native_realization

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

theorem k326AtlasData_holds :
    K326AtlasData := by
  have hON : Nat.card CFSG.Blueprint.NativeSporadic.ON = 460815505920 := CFSG.Sporadic.ON.card_ON
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 443520 := CFSG.Sporadic.Mathieu.card_M22
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card CFSG.Blueprint.NativeSporadic.M22 ≠ 0
      rw [hM]; norm_num)
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    Nat.finite_of_card_ne_zero (by
      show Nat.card CFSG.Blueprint.NativeSporadic.ON ≠ 0
      rw [hON]; norm_num)
  refine ⟨fun α hα => CFSG.ASVolI.burnsideA315x_out_alt (by norm_num) (by norm_num)
      (MulEquiv.refl _) α hα,
    fun α hα => CFSG.ASVolI.burnsideA315x_out_alt (by norm_num) (by norm_num)
      (MulEquiv.refl _) α hα,
    fun α hα => CFSG.ASVolI.burnsideA315s_oddInner_M22 (MulEquiv.refl _) α hα,
    ?_, ?_, ?_, CFSG.Sporadic.Mathieu.card_M22, hON⟩
  · refine CFSG.ASVolI.burnsideA315s_oddInner_of_not_dvd ?_
    intro p hp hp2 hdvd
    have h4 : p ∣ 4 := hdvd.trans CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1
    have : p ∣ 2 ^ 2 := by simpa using h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  · rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide

theorem lieSporSimple_holds :
    LieSporSimple := by
  refine ⟨fun X _ t a p f h => (CFSG.LieType.Catalog.lieModel_finite_simple X t a p f h).2.2, ?_⟩
  intro s hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .M11 (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .M12 (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .M22 (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .M23 (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .M24 (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .J2 (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .HS (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .He (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .Ru (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .J4 (by decide)).2.2
  · exact (CFSG.Milestones.native_carrier_finite_simple_of_ne_B .J3 (by decide)).2.2

theorem k326P1_holds
    (h334 : K334Cover) : K326P1 :=
  K326P1_of_inputs h334 k326AtlasData_holds

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

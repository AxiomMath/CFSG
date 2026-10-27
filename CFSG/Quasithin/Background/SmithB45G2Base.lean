module

public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.F9Tilde

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

theorem qhatOf_le_one_of_rAV_le_one (hV : ∀ v : V, v ^ 2 = 1) {X E : Subgroup (MulAut V)}
    (hE : IsA2 X E) (hr : rAV E ≤ 1) : qhatOf X ≤ ((1 : ℚ) : WithTop ℚ) := by
  obtain ⟨B, -, hB, hrB⟩ := exists_offender_rAV_le hV hE hr
  obtain ⟨A₀, hle, hmin⟩ := B1.exists_isFFStarMin_le hB
  have hquad : IsQuadratic A₀ := B1_4_3 hV hmin
  have hr0 : rAV A₀ ≤ rAV B :=
    rAV_le_of_card_le hV hB.isA2 hle.1 hle.2.2.1 (B1_4_1 hV hB) (le_of_eq hle.2.2.2.symm)
  exact (qhatOf_le_qOf X).trans
    (qOf_le_iff.2 ⟨A₀, hmin.1.isA2, hquad, (hr0.trans hrB).trans hr⟩)

theorem exists_cubic_of_qhatOf_le_two (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hq : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) :
    ∃ A, IsA2 X A ∧ commSeries A 3 = ⊥ ∧
      Nat.card V ≤ Nat.card A ^ 2 * Nat.card (fixV A) := by
  obtain ⟨A, hA, hc, hr⟩ := kq_le_iff.mp hq
  exact ⟨A, hA, hc, (rAV_le_two_iff hV hA).1 hr⟩

end CFSG.Quasithin

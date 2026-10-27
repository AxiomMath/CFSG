module

public import CFSG.Quasithin.MS93.S46R468M4
public import CFSG.Quasithin.MS93.S46R468Deg
public import CFSG.Quasithin.MS93.S46R468Q2

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46

theorem s468_of (h43 : S43) (h463 : I463) (h464 : I464) (h465 : I465) (h466a : I466a)
    (h467 : I467) (hDeg : S468Deg) : S46.S468 := by
  refine s468_of_s468At fun G _ _ M T L F _ _ φ c α β hα hαβ => ?_
  by_contra h
  by_cases hq2 : Fintype.card F = 2
  · obtain ⟨α', hc, hg1, hbad⟩ := exists_crit_of_not_s468At h43 h467 c hα hαβ h
    exact false_of_two h463 h464 h465 h466a c hc (by rw [hg1]; exact hbad) hq2
  have hq4 : 4 ≤ Fintype.card F := by
    have := four_le_card_of_isSL3FullVia c.via (by rwa [Nat.card_eq_fintype_card])
    rwa [Nat.card_eq_fintype_card] at this
  refine h (hDeg G M T L F φ c α β hα hαβ fun α' hc hg1 hbad => ?_)
  by_contra hnd
  rw [not_or, not_not, not_not] at hnd
  subst hg1
  exact BadConf.false_of_four h464 h465 h466a ⟨hc, hbad, hnd.1⟩ hnd.2 hq4

end CFSG.Quasithin.MS93.S46R

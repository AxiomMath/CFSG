module

public import CFSG.RankThree.PartOne.KS.LyFiveCore
public import CFSG.RankThree.PartOne.S11c.SporadicFiveFixed
public import CFSG.RankThree.PartOne.SPOR.OuterLy

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.Sporadic.Ly CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.HNRed

theorem lyFiveFixed :
    LyFiveFixed := by
  refine noFiveFixedPSU3_of_bad ?_ ?_
  · intro T _ _ e α hα
    have hdvd : Nat.card (Outer T) ∣ 2 := (SPOR.outer_order_divides_two' (T := T) ⟨e⟩).1
    exact exists_conj_of_pow_five (Nat.le_of_dvd (by norm_num) hdvd |>.trans (by norm_num)) hα
  · intro T _ _ e b hb K hK hcard
    have e' : T ≃* J := by exact e.trans lyEquivJ
    have h1 := @card_dvd_centralizer_of_equiv T J _ inferInstance e' b K hK
    rw [hcard] at h1
    have hw : orderOf (e' b) = 5 := @orderOf_equiv_eq_five T J _ inferInstance e' b hb
    rcases lyFive_card_centralizer hw with h | h <;> rw [h] at h1 <;> omega

end CFSG.RankThree.PartOne.LyFive

module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ExcBasic
public import CFSG.Sporadic.Schreier.TitsOuterTwo
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
import CFSG.RankThree.PartTwo.Sec13.K135K3Core

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

open CFSG.RankThree.PartTwo.Sec13.KF135Proof

theorem card_dvd_of_le_inn {S : Type} [Group S] [Finite S] {P : Subgroup (MulAut S)}
    (hP : P ≤ (MulAut.conj : S →* MulAut S).range) : Nat.card P ∣ Nat.card S :=
  (Subgroup.card_dvd_of_le hP).trans (Subgroup.card_range_dvd _)

theorem not_sq_dvd_card_tits {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) : ¬ p ^ 2 ∣ 17971200 := by
  intro h2
  have hp1 : p ∣ 2 ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 := by
    rw [show (2 : ℕ) ^ 11 * 3 ^ 3 * 5 ^ 2 * 13 = 17971200 by norm_num]
    exact (dvd_pow_self p two_ne_zero).trans h2
  have hp13 : p = 13 := by
    rcases (Nat.Prime.dvd_mul hp).1 hp1 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
          omega
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
          omega
      · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
        omega
    · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
  subst hp13
  exact absurd h2 (by norm_num)


theorem false_of_kF135Hyp_tits {S : Type} [Group S] [Finite S] {p : ℕ}
    {P : Subgroup (MulAut S)} {x u : MulAut S} {V : Subgroup (MulAut S)}
    {ht : TauCeti.LieTypeIndex.tits.Valid}
    (e : S ≃* (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group) (h : KF135Hyp S p P x u V) : False := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hS, -, hout, -⟩ := CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound S 2 1
    (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits ht e)
  have hP : P ≤ (MulAut.conj : S →* MulAut S).range :=
    CFSG.RankThree.PartTwo.Sec13.F135Last.inner_of_not_dvd_outer hp
      (by
        rw [hout]
        intro hd
        have := Nat.le_of_dvd (by norm_num) hd
        have := h.seven_le
        omega) P h.pgroup
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.pgroup
  have hdvd : p ^ k ∣ 17971200 := by
    rw [← hk, ← hS]
    exact card_dvd_of_le_inn hP
  have hk3 : 3 ≤ k := by
    have h3 := h.card
    rw [hk] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  exact not_sq_dvd_card_tits hp h.seven_le ((pow_dvd_pow p (by omega)).trans hdvd)

theorem kF135At_fam7Tits : KF135At Fam7Tits := by
  intro S _ _ p P x u V hS h
  obtain ⟨ht, ⟨e⟩⟩ := hS
  exact (false_of_kF135Hyp_tits e h).elim

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2Exc

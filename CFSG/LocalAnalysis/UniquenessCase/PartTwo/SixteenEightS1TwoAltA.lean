module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16e_two_alt_not_dvd_six_factorial {p n : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hn6 : n ≠ 6) :
    ¬ p ^ 3 ∣ 6 * Nat.factorial n := by
  intro h
  have hp5 : 5 ≤ p := hpp.five_le_of_ne_two_of_ne_three hp2 hp3
  have hpdvd : p ∣ 6 * Nat.factorial n := (dvd_pow_self p (by norm_num)).trans h
  have hp_not6 : ¬ p ∣ 6 := by
    intro h6
    have h23 : p ∣ 2 ∨ p ∣ 3 := by
      have : p ∣ 2 * 3 := by simpa using h6
      exact hpp.dvd_mul.mp this
    rcases h23 with h2 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h3)
  have hfac : p ∣ Nat.factorial n := by
    rcases hpp.dvd_mul.mp hpdvd with h6 | hfac
    · exact absurd h6 hp_not6
    · exact hfac
  have hpn : p ≤ n := (hpp.dvd_factorial).mp hfac
  have hp11 : p ≤ 11 := by omega
  interval_cases p <;> interval_cases n <;>
    first
      | (norm_num at h; done)
      | (norm_num at hpp; done)

theorem s16e_two_alt_card_mbar (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 6 * Nat.factorial n :=
  s16e_two_fam_alt_card_mbar D hx h61 h127 h1214 hV hset hL hs hn5 hn6 hA hsum

theorem s16e_two_alt_sig (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    D.sig = {3} := by
  have hcard := s16e_two_alt_card_mbar D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hn5 hn11
    hn6 hA hsum
  have hkey : ∀ p ∈ D.sig, p = 3 := by
    intro p hp
    obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
    by_contra hp3
    have hp5 : 5 ≤ p := hpp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hpr := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hset.hyp16 hV h4 hp
    obtain ⟨E, hEA, -, hEcard⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt (Mbar D.M V₀ V hV)
    have hdvdE : p ^ 3 ∣ Nat.card E := by
      rw [hEcard]
      exact pow_dvd_pow p hpr
    have hdvdV : p ^ 3 ∣ Nat.card ↥(Mbar D.M V₀ V hV) :=
      hdvdE.trans (Subgroup.card_dvd_of_le hEA)
    have hcardeq : Nat.card ↥(Mbar D.M V₀ V hV) =
        Nat.card ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
      (c23_card_mbar_v1Sub_eq D (r1217_of_twelve_seventeen D hx h61 h127 h1214) hset.hyp151 hV).symm
    have hdvd : p ^ 3 ∣ 6 * Nat.factorial n := by
      rw [hcardeq] at hdvdV
      exact hdvdV.trans hcard
    exact s16e_two_alt_not_dvd_six_factorial hpp hp2 hp3 hn5 hn11 hn6 hdvd
  obtain ⟨q, hq⟩ := hx.sig_nonempty
  ext p
  simp only [Set.mem_singleton_iff]
  exact ⟨hkey p, fun hp => by rw [hp]; exact (hkey q hq) ▸ hq⟩

theorem s16e_two_alt_kbar (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    IsSym ↥(kBar D.M V₀ V hV L) 3 := by
  have hsig := s16e_two_alt_sig D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hn5 hn11 hn6 hA
    hsum
  exact (s16e_two_fam_alt_route D hx h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [hsig]; exact Set.mem_singleton 3) hn5 hn6 hA hsum).1

theorem s16e_two_alt_direct (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1214 : F12.R1214 D) (h638 : UC6.R6_38 D)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L)
    (hL : barSub V₀ V hV L ≠ ⊥) (hconc : Conc4_136 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 1) {n : ℕ} (hn5 : 5 ≤ n) (hn11 : n ≤ 11) (hn6 : n ≠ 6)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z n)
      (lStar D.M V₀ V hV L) (wStar D.M V₀ V hV L) ⊥ 2) :
    ∃ L₀ : Subgroup (MulAut (Vtil V₀ V hV)),
      IsInternalDirect (kBar D.M V₀ V hV L) L₀ (Mbar D.M V₀ V hV) ∧ IsSym ↥L₀ n := by
  have hsig := s16e_two_alt_sig D hx h4 h61 h127 h1214 h638 hV hset hL hconc hs hn5 hn11 hn6 hA
    hsum
  exact (s16e_two_fam_alt_route D hx h61 h127 h1214 h638 hV hset hL hconc hs
    (by rw [hsig]; exact Set.mem_singleton 3) hn5 hn6 hA hsum).2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

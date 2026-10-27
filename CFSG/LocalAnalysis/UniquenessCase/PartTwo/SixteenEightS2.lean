module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightFix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16e_false_of_sig_pRank_three {D : Data G} (hx : DataExt D)
    (h4 : 3 < CFSG.Open.evenRank G) {p : ℕ} (hsig : D.sig = {p})
    (hrk : CFSG.Open.pRank p D.M = 3) : False := by
  have hp : p ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton p
  have := hx.four_le h4 p hp
  omega

theorem s16e_not_case164_2 {D : Data G} (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
    (h : Case164_2 D V₀ V hV L) : False :=
  s16e_false_of_sig_pRank_three hx h4 h.2.1 h.2.2.1

theorem s16e_not_case164_3 {D : Data G} (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
    (h : Case164_3 D V₀ V hV L) : False :=
  s16e_false_of_sig_pRank_three hx h4 h.2.2.1 h.2.2.2.1

theorem s16e_not_case164_4 {D : Data G} (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
    (h : Case164_4 D V₀ V hV L) : False := by
  obtain ⟨p, -, -, -, hsig, hrk, -⟩ := h
  exact s16e_false_of_sig_pRank_three hx h4 hsig hrk

theorem s16e_not_case153_2 {D : Data G} (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
    (h : Case153_2 D V₀ V hV L) : False := by
  obtain ⟨-, p, -, -, -, hsig, hrk, -⟩ := h
  exact s16e_false_of_sig_pRank_three hx h4 hsig hrk

theorem s16e_exists_pRank_mBar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    (h4 : 3 < CFSG.Open.evenRank G) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := by
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  exact ⟨p, (D.sig_prime p hp).1, (D.sig_prime p hp).2,
    s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 h16 hV h4 hp⟩

theorem s16e_s2_153_3 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hconc : Conc4_136 D V₀ V hV L) (h : Case153_3 D V₀ V hV L)
    (hs : s15 D.M V₀ V hV L = 2) : False := by
  obtain ⟨hcard, hrk⟩ := r1613g_case153_3_summary D hconc h
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hcard]
    decide
  obtain ⟨p, hp, hp2, h3⟩ := s16e_exists_pRank_mBar D hx h61 h127 hset.hyp16 hV h4
  have := s16e_pRank_mBar_lt_three_of_rk_le_two D h1217 hV hset hL
    (s16e_v1Sub_eq_of_odd D hV hodd) hs hrk hp hp2
  omega

theorem s16e_s2_163_12 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (h : Case163_12 D V₀ V hV L) (hs : s15 D.M V₀ V hV L = 2) : False := by
  obtain ⟨hc, hrk, -⟩ := h
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hc.2]
    decide
  obtain ⟨p, hp, hp2, h3⟩ := s16e_exists_pRank_mBar D hx h61 h127 hset.hyp16 hV h4
  have := s16e_pRank_mBar_lt_three_of_rk_three D h1217 hV hset hL
    (s16e_v1Sub_eq_of_odd D hV hodd) hs hrk hp hp2
  omega

theorem s16e_s2_false_of_odd (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) (hrk : 3 < rk ↥(wTil V₀ V hV L))
    (hγ : gamma15 D.M V₀ V hV L ≤ 3) : False := by
  have := s16e_gamma15_eq_of_odd D hV hodd
  omega

theorem s16e_odd_card_of_elemAbelianOfRank {X : Type} [Group X] {p r : ℕ} [NeZero p]
    (hE : IsElemAbelianOfRank p r X) (hp : Odd p) : Odd (Nat.card X) := by
  rw [s16c167_card_isElemAbelianOfRank hE]
  exact hp.pow

theorem s16e_one_le_of_elemAbelianOfRank {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup G} {p r : ℕ} [NeZero p] (hL : barSub V₀ V hV L ≠ ⊥)
    (hE : IsElemAbelianOfRank p r ↥(lBar V₀ V hV L)) : 1 ≤ r := by
  by_contra h0
  have hr : r = 0 := by omega
  subst hr
  have hc := s16c167_card_isElemAbelianOfRank hE
  rw [pow_zero] at hc
  exact hL (Subgroup.card_eq_one.1 hc)

theorem s16e_s2_162_1 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Case162_1 D V₀ V hV L) (hγ : gamma15 D.M V₀ V hV L ≤ 3) : False := by
  obtain ⟨hcase, -⟩ := h
  have h1 : gamma15 D.M V₀ V hV L = rk ↥(wStar D.M V₀ V hV L) := rfl
  rcases hcase with ⟨n, hn5, -, -, hsum⟩ | ⟨-, hsum⟩
  · have h2 := s16c1610_le_rk_sumOfNat_two (r := 3)
      (fun I hI => by
        have := s16c1610_le_rk_alternatingNatural (by omega : 2 ≤ n) hI
        omega) hsum
    omega
  · have h2 := s16c1610_le_rk_sumOfNat_two (r := 3)
      (fun I hI => by
        have := s16c1610_rk_binaryNaturalSL hI
        omega) hsum
    omega

theorem s16e_s2_162_8 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Case162_8 D V₀ V hV L) (hγ : gamma15 D.M V₀ V hV L ≤ 3) : False := by
  obtain ⟨hcase, -⟩ := h
  have h1 : gamma15 D.M V₀ V hV L = rk ↥(wStar D.M V₀ V hV L) := rfl
  rcases hcase with ⟨-, hnat⟩ | ⟨-, hnat⟩
  · have := s16c1610_rk_binaryNaturalSL hnat
    omega
  · have := s16c1610_rk_natOmegaMinus (by norm_num) hnat
    omega

theorem s16e_s2_163_4 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Case163_4 D V₀ V hV L) (hγ : gamma15 D.M V₀ V hV L ≤ 3) : False := by
  obtain ⟨-, hnat, -⟩ := h
  have h1 : gamma15 D.M V₀ V hV L = rk ↥(wStar D.M V₀ V hV L) := rfl
  have := s16c1610_rk_binaryNaturalSL hnat
  omega

theorem s16e_s2_163_3 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Case163_3 D V₀ V hV L) (hγ : gamma15 D.M V₀ V hV L ≤ 3) : False := by
  obtain ⟨-, hnat, -⟩ := h
  have h1 := s16e_gamma15_eq_of_inf_fixV D hV (s16e_inf_fixV_eq_bot_natOmegaMinus hnat)
  have h2 := s16c1610_rk_natOmegaMinus (by norm_num) hnat
  omega

theorem s16e_s2_163_5 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (h : Case163_5 D V₀ V hV L) (hγ : gamma15 D.M V₀ V hV L ≤ 3) : False := by
  obtain ⟨hcase, -⟩ := h
  have h1 : gamma15 D.M V₀ V hV L = rk ↥(wStar D.M V₀ V hV L) := rfl
  rcases hcase with ⟨-, hsum⟩ | ⟨-, hsum⟩
  · have h2 := s16e_rk_sumOfNat_ge (b := 3)
      (fun I hI => by
        have := s16c1610_rk_binaryNaturalSL hI
        omega) hsum
    omega
  · have h2 := s16e_rk_sumOfNat_ge (b := 3)
      (fun I hI => by
        have := s16c1610_le_rk_alternatingNatural (by norm_num : 2 ≤ 5) hI
        omega) hsum
    omega

theorem s16e_s2_concl168 (D : Data G) (hx : DataExt D) (h4 : 3 < CFSG.Open.evenRank G)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hset : Setting16 D V₀ V L) (hL : barSub V₀ V hV L ≠ ⊥)
    (hconc : Conc4_136 D V₀ V hV L) (h163 : Concl163 D V₀ V hV L)
    (h164 : Concl164 D V₀ V hV L) : Concl168 D V₀ V hV L := by
  obtain ⟨hs2, hγ⟩ := h164
  have hγ3 : gamma15 D.M V₀ V hV L ≤ 3 := by
    rcases hγ with h | h | h | h
    · exact h
    · exact (s16e_not_case164_2 hx h4 h).elim
    · exact (s16e_not_case164_3 hx h4 h).elim
    · exact (s16e_not_case164_4 hx h4 h).elim
  rcases h163 with h162 | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h162 with h153 | h | h | h | h | h | h | h | h | h
    · rcases h153 with h | h | h
      · exact absurd h.2.2.2.2.1 (by omega)
      · exact (s16e_not_case153_2 hx h4 h).elim
      · exact (s16e_s2_153_3 D hx h4 h61 h127 h1217 hset hL hconc h hs2).elim
    · exact (s16e_s2_162_1 D h hγ3).elim
    · exact absurd h.1 (by omega)
    · obtain ⟨hc, hrk, -⟩ := h
      exact (s16e_s2_false_of_odd D (by rw [hc.2]; decide) (by omega) hγ3).elim
    · obtain ⟨hP, hrk, -⟩ := h
      exact (s16e_s2_false_of_odd D (by rw [hP.2.1]; decide) (by omega) hγ3).elim
    · obtain ⟨⟨r, hE, hrk⟩, -⟩ := h
      have hr := s16e_one_le_of_elemAbelianOfRank hL hE
      exact (s16e_s2_false_of_odd D (s16e_odd_card_of_elemAbelianOfRank hE (by decide))
        (by omega) hγ3).elim
    · exact absurd h.2.2.1 (by omega)
    · exact absurd h.2.2 (by omega)
    · exact (s16e_s2_162_8 D h hγ3).elim
    · exact absurd h.2.2.1 (by omega)
  · exact absurd h.2.1 (by omega)
  · exact absurd h.2.2 (by omega)
  · exact (s16e_s2_163_3 D h hγ3).elim
  · exact (s16e_s2_163_4 D h hγ3).elim
  · exact (s16e_s2_163_5 D h hγ3).elim
  · exact absurd h.2.2.1 (by omega)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact absurd h.2.2.1 (by omega)
  · obtain ⟨hc, hrk, -⟩ := h
    exact (s16e_s2_false_of_odd D (by rw [hc.2]; decide) (by omega) hγ3).elim
  · obtain ⟨hE, hrk⟩ := h
    exact (s16e_s2_false_of_odd D (s16e_odd_card_of_elemAbelianOfRank hE (by decide))
      (by omega) hγ3).elim
  · obtain ⟨r, hE, hrk⟩ := h
    have hr := s16e_one_le_of_elemAbelianOfRank hL hE
    exact (s16e_s2_false_of_odd D (s16e_odd_card_of_elemAbelianOfRank hE (by decide))
      (by omega) hγ3).elim
  · exact (s16e_s2_163_12 D hx h4 h61 h127 h1217 hset hL h hs2).elim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

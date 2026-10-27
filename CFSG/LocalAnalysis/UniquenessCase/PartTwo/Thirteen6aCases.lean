module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aCtx
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aF
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aPair
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aSp
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Thirteen6aU3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
import CFSG.LocalAnalysis.UniquenessCase.UC1K337
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3S13
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3Types
import CFSG.LocalAnalysis.UniquenessCase.UC22S2121E3U3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s136a_false_of_one_member
    {D : Data G}
    {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V} (c : Ctx D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig)
    (hp3 : p ≠ 3) {L : Subgroup G} (hL : L ∈ calC D.M) (hpL : p ∣ Nat.card (barImage D.M L))
    (hsum : CFSG.Open.pRank p D.M = CFSG.Open.pRank p L + CFSG.Open.pRank p (F13.Sp D.M p)) :
    False := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hS1 : CFSG.Open.pRank p (F13.Sp D.M p) ≤ 1 := c.s13.hyp131.smallS p hp
  have h3M : 3 ≤ CFSG.Open.pRank p D.M := c.ext.three_le p hp
  have hL2 : 2 ≤ CFSG.Open.pRank p L := by omega
  rcases uc22s2121e3_pRank_le_of_mem_calC c.s13.hyp131 hpp hp2 hL with
    hL1 | ⟨⟨n, hn, hU, hpn⟩, hL2'⟩
  · omega
  have hSp1 : 1 ≤ CFSG.Open.pRank p (F13.Sp D.M p) := by omega
  have hSp : F13.Sp D.M p ≠ ⊥ := by
    intro hbot
    have h0 : CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := s13_Rank13_pRank_bot hpp
    rw [hbot] at hSp1
    omega
  have hdiv : p ∣ 2 ^ (2 * n) - 1 := by
    rw [uc22p20o_two_pow_two_mul_sub_one n]
    exact dvd_mul_of_dvd_right hpn (2 ^ n - 1)
  have hEL := s136a_exists_permutes_of_isSU3 (s13_le_of_mem_calC hL)
    (c.s13.hyp131.normal L hL) (uc22p22d_isSU3_of_isU3 hL.2.2 hU) hpp hp2 hp3 hdiv
  have hES := s136a_exists_permutes_of_Sp hV c.thin c.cyc c.s13 c.r638 c.r332 c.r22 c.r23 hp hSp
  obtain ⟨X, hX⟩ := s136a_inP11_of_member_Sp c.thin c.s13 c.sg hp hL hpL hEL hES
  exact s136a_false_of_inP11_of_isU3 c.r1 c.r333 hL hU hX

private theorem s136a_dvd_two_pow_add_one_iff {p n : ℕ} :
    p ∣ 2 ^ n + 1 ↔ (2 : ZMod p) ^ n = -1 := by
  have hcast : ((2 ^ n + 1 : ℕ) : ZMod p) = (2 : ZMod p) ^ n + 1 := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [← ZMod.natCast_eq_zero_iff (2 ^ n + 1) p, hcast, add_eq_zero_iff_eq_neg]

private theorem s136a_dvd_two_pow_mul_two_sub_one {D : Data G} {p : ℕ}
    (hH : F13.Hyp131 D) (hpp : p.Prime) (hp2 : p ≠ 2) {L K J : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hJ : J ∈ calC D.M)
    (h2 : CFSG.Open.pRank p L = 2 ∨ CFSG.Open.pRank p K = 2)
    (hpJ : p ∣ Nat.card (barImage D.M J)) {m : ℕ} (hm : IsPowTwo m) (hJU : IsU3 (Bar2 J) m) :
    p ∣ 2 ^ (2 * m) - 1 := by
  obtain ⟨n', hn', hpn'⟩ : ∃ n', IsPowTwo n' ∧ p ∣ 2 ^ n' + 1 := by
    rcases h2 with h2 | h2
    · rcases uc22s2121e3_pRank_le_of_mem_calC hH hpp hp2 hL with
        h1 | ⟨⟨n', hn', -, hpn'⟩, -⟩
      · omega
      · exact ⟨n', hn', hpn'⟩
    · rcases uc22s2121e3_pRank_le_of_mem_calC hH hpp hp2 hK with
        h1 | ⟨⟨n', hn', -, hpn'⟩, -⟩
      · omega
      · exact ⟨n', hn', hpn'⟩
  have hcard : p ∣ Nat.card (Bar2 J) := by
    obtain ⟨e⟩ := s13_bar_equiv hJ
    rwa [Nat.card_congr e.toEquiv]
  have h1 : (2 : ZMod p) ^ (2 * m) = 1 :=
    (InS3.k337_holds p hpp hp2 n' m hn' hm).2.2.1
      (s136a_dvd_two_pow_add_one_iff.mp hpn') (Bar2 J) hJU hcard
  exact (CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mpr h1

private theorem s136a_case_i_l2 {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (c : Ctx D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hpK : p ∣ Nat.card (barImage D.M K)) {n : ℕ} (hU : IsU3 (Bar2 L) n) {m' : ℕ}
    (hm' : IsPowTwo m') (hK2 : IsL2 (Bar2 K) m')
    (hEL : ∃ E ≤ L, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧ Permutes E D.T)
    (hSp : F13.Sp D.M p = ⊥)
    (hab : CFSG.Open.pRank p L = 2 ∨ CFSG.Open.pRank p K = 2) :
    ∃ m, IsPowTwo m ∧ p ∣ 2 ^ m + 1 ∧ IsU3 (Bar2 L) m ∧ IsL2 (Bar2 K) m ∧
      F13.Sp D.M p = ⊥ := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hpK' : p ∣ Nat.card (Bar2 K) := by
    obtain ⟨e⟩ := s13_bar_equiv hK
    rwa [Nat.card_congr e.toEquiv]
  rw [S17.card_of_isL2 hK2] at hpK'
  have hp2m : ¬ p ∣ 2 ^ m' := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
  have h2m : p ∣ 2 ^ (2 * m') - 1 := by
    rcases (Nat.Prime.dvd_mul hpp).mp hpK' with h | h
    · exact absurd h hp2m
    · exact h
  have hfac : 2 ^ (2 * m') - 1 = (2 ^ m' - 1) * (2 ^ m' + 1) := by
    rw [show 2 ^ (2 * m') = (2 ^ m') ^ 2 by rw [pow_mul']]
    rw [show (2 ^ m') ^ 2 - 1 = (2 ^ m' + 1) * (2 ^ m' - 1) by
      simpa using Nat.sq_sub_sq (2 ^ m') 1]
    exact mul_comm _ _
  rcases (Nat.Prime.dvd_mul hpp).mp (hfac ▸ h2m) with hsub | hadd
  · have hE_K : ∃ E ≤ K, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧ Permutes E D.T :=
      s136a_exists_permutes_of_isL2 (s13_le_of_mem_calC hK) (c.s13.hyp131.normal K hK) hK2
        hpp hp2 hsub
    obtain ⟨X, hX⟩ := s136a_inP11_of_members c.thin c.s13 c.sg hp hL hK hne hEL hE_K
    exact (s136a_false_of_inP11_of_isU3 c.r1 c.r333 hL hU hX).elim
  · have hneg : (2 : ZMod p) ^ m' = -1 := s136a_dvd_two_pow_add_one_iff.mp hadd
    have hb1 : CFSG.Open.pRank p K ≤ 1 := by
      rcases uc22s2121e3_pRank_le_of_mem_calC c.s13.hyp131 hpp hp2 hK with
        h | ⟨⟨n', -, hKU', -⟩, -⟩
      · exact h
      · exact absurd hK2 (not_isL2_of_isU3 hKU')
    have ha2 : CFSG.Open.pRank p L = 2 := by rcases hab with h | h <;> omega
    have hLUex : ∃ n', IsPowTwo n' ∧ IsU3 (Bar2 L) n' ∧ p ∣ 2 ^ n' + 1 := by
      rcases uc22s2121e3_pRank_le_of_mem_calC c.s13.hyp131 hpp hp2 hL with h | h
      · omega
      · exact h.1
    obtain ⟨n', hn', hLU', hpn'⟩ := hLUex
    have hn'm' : n' = m' :=
      (InS3.k337_holds p hpp hp2 n' m' hn' hm').2.1
        (s136a_dvd_two_pow_add_one_iff.mp hpn') hneg
    exact ⟨m', hm', hadd, hn'm' ▸ hLU', hK2, hSp⟩

private theorem s136a_case_i
    {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (c : Ctx D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hpL : p ∣ Nat.card (barImage D.M L)) (hpK : p ∣ Nat.card (barImage D.M K)) {n : ℕ}
    (hU : IsU3 (Bar2 L) n) (h2n : p ∣ 2 ^ (2 * n) - 1)
    (hsum : CFSG.Open.pRank p D.M = CFSG.Open.pRank p L + CFSG.Open.pRank p K +
      CFSG.Open.pRank p (F13.Sp D.M p)) {m' : ℕ} (hm' : IsPowTwo m')
    (hKs : IsL2 (Bar2 K) m' ∨ IsU3 (Bar2 K) m') :
    ∃ m, IsPowTwo m ∧ p ∣ 2 ^ m + 1 ∧ IsU3 (Bar2 L) m ∧ IsL2 (Bar2 K) m ∧
      F13.Sp D.M p = ⊥ := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hEL : ∃ E ≤ L, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧ Permutes E D.T :=
    s136a_exists_permutes_of_isSU3 (D := D) (K := L) (n := n) (r := p)
      (s13_le_of_mem_calC hL) (c.s13.hyp131.normal L hL)
      (uc22p22d_isSU3_of_isU3 hL.2.2 hU) hpp hp2 hp3 h2n
  have hSp : F13.Sp D.M p = ⊥ := by
    by_contra hSp
    obtain ⟨E, hES⟩ := s136a_exists_permutes_of_Sp hV c.thin c.cyc c.s13 c.r638 c.r332 c.r22
      c.r23 hp hSp
    obtain ⟨X, hX⟩ := s136a_inP11_of_member_Sp c.thin c.s13 c.sg hp hL hpL hEL ⟨E, hES⟩
    exact s136a_false_of_inP11_of_isU3 c.r1 c.r333 hL hU hX
  have hs : CFSG.Open.pRank p (F13.Sp D.M p) = 0 := by
    rw [hSp]
    exact s13_Rank13_pRank_bot hpp
  have ha : CFSG.Open.pRank p L ≤ 2 := by
    rcases uc22s2121e3_pRank_le_of_mem_calC c.s13.hyp131 hpp hp2 hL with
      h | ⟨-, h⟩ <;> omega
  have hb : CFSG.Open.pRank p K ≤ 2 := by
    rcases uc22s2121e3_pRank_le_of_mem_calC c.s13.hyp131 hpp hp2 hK with
      h | ⟨-, h⟩ <;> omega
  have hab : CFSG.Open.pRank p L = 2 ∨ CFSG.Open.pRank p K = 2 := by
    have h3 := c.ext.three_le p hp
    omega
  rcases hKs with hK2 | hKU
  · exact s136a_case_i_l2 c hp hL hK hne hpK hU hm' hK2 hEL hSp hab
  · have hE_K : ∃ E ≤ K, IsElemAbelian p E ∧ 1 ≤ CFSG.Open.pRank p E ∧ Permutes E D.T :=
      s136a_exists_permutes_of_isSU3 (D := D) (K := K) (n := m') (r := p)
        (s13_le_of_mem_calC hK) (c.s13.hyp131.normal K hK)
        (uc22p22d_isSU3_of_isU3 hK.2.2 hKU) hpp hp2 hp3
        (s136a_dvd_two_pow_mul_two_sub_one c.s13.hyp131 hpp hp2 hL hK hK hab hpK hm' hKU)
    obtain ⟨X, hX⟩ := s136a_inP11_of_members c.thin c.s13 c.sg hp hL hK hne hEL hE_K
    exact (s136a_false_of_inP11_of_isU3 c.r1 c.r333 hL hU hX).elim

private theorem s136a_case_ii {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (c : Ctx D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hpL : p ∣ Nat.card (barImage D.M L)) (hpK : p ∣ Nat.card (barImage D.M K)) {n : ℕ}
    (hn : IsPowTwo n) (hU : IsU3 (Bar2 L) n) (h2n : ¬ p ∣ 2 ^ (2 * n) - 1)
    (hsum : CFSG.Open.pRank p D.M = CFSG.Open.pRank p L + CFSG.Open.pRank p K +
      CFSG.Open.pRank p (F13.Sp D.M p)) {m' : ℕ} (hm' : IsPowTwo m')
    (hKs : IsL2 (Bar2 K) m' ∨ IsU3 (Bar2 K) m') : False := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  by_cases h4 : 3 < CFSG.Open.evenRank G
  · have h4' := c.ext.four_le h4 p hp
    have hs := c.s13.hyp131.smallS p hp
    have ha : CFSG.Open.pRank p L ≤ 2 := by
      rcases uc22s2121e3_pRank_le_of_mem_calC c.s13.hyp131 hpp hp2 hL with
        h | ⟨-, h⟩ <;> omega
    have hb : CFSG.Open.pRank p K ≤ 2 := by
      rcases uc22s2121e3_pRank_le_of_mem_calC c.s13.hyp131 hpp hp2 hK with
        h | ⟨-, h⟩ <;> omega
    have hab : CFSG.Open.pRank p L = 2 ∨ CFSG.Open.pRank p K = 2 := by omega
    exact h2n
      (s136a_dvd_two_pow_mul_two_sub_one c.s13.hyp131 hpp hp2 hL hK hL hab hpL hn hU)
  · have he : CFSG.Open.evenRank G ≤ 3 := by omega
    exact uc22s2121e3u3_false he (s13_normalSimple c.thin D c.s13) hL hK hne hpp hp2 hn hU h2n
      hpL hm' hKs hpK

theorem s136a_case_u3
    {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (c : Ctx D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) (hp3 : p ≠ 3) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hpL : p ∣ Nat.card (barImage D.M L)) (hpK : p ∣ Nat.card (barImage D.M K)) {n : ℕ}
    (hn : IsPowTwo n) (hU : IsU3 (Bar2 L) n)
    (hsum : CFSG.Open.pRank p D.M = CFSG.Open.pRank p L + CFSG.Open.pRank p K +
      CFSG.Open.pRank p (F13.Sp D.M p)) :
    ∃ m, IsPowTwo m ∧ p ∣ 2 ^ m + 1 ∧ IsU3 (Bar2 L) m ∧ IsL2 (Bar2 K) m ∧
      F13.Sp D.M p = ⊥ := by
  obtain ⟨m', hm', hKs⟩ := c.shape K hK
  by_cases h2n : p ∣ 2 ^ (2 * n) - 1
  · exact s136a_case_i c hp hp3 hL hK hne hpL hpK hU h2n hsum hm' hKs
  · exact (s136a_case_ii c hp hL hK hne hpL hpK hn hU h2n hsum hm' hKs).elim

theorem s136a_case_l2l2
    {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (c : Ctx D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) (h3 : 3 ∉ D.sig) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hpL : p ∣ Nat.card (barImage D.M L)) (hpK : p ∣ Nat.card (barImage D.M K)) {n m : ℕ}
    (hn : IsPowTwo n) (hm : IsPowTwo m) (hLs : IsL2 (Bar2 L) n) (hKs : IsL2 (Bar2 K) m)
    (hsum : CFSG.Open.pRank p D.M = CFSG.Open.pRank p L + CFSG.Open.pRank p K +
      CFSG.Open.pRank p (F13.Sp D.M p)) :
    n = m ∧ p ∣ 2 ^ n + 1 ∧ F13.Sp D.M p ≠ ⊥ := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hL1 := s136a_pRank_le_one_of_isL2 c.s13.hyp131 hpp hp2 hL hLs
  have hK1 := s136a_pRank_le_one_of_isL2 c.s13.hyp131 hpp hp2 hK hKs
  have hSp1 : 1 ≤ CFSG.Open.pRank p (F13.Sp D.M p) := by
    have h3M : 3 ≤ CFSG.Open.pRank p D.M := c.ext.three_le p hp
    omega
  have hSp : F13.Sp D.M p ≠ ⊥ := by
    intro hbot
    have h0 : CFSG.Open.pRank p (⊥ : Subgroup G) = 0 := s13_Rank13_pRank_bot hpp
    rw [hbot] at hSp1
    omega
  have hcardL : p ∣ Nat.card (Bar2 L) := by
    obtain ⟨e⟩ := s13_bar_equiv hL
    exact (Nat.card_congr e.toEquiv).symm ▸ hpL
  have hcardK : p ∣ Nat.card (Bar2 K) := by
    obtain ⟨e⟩ := s13_bar_equiv hK
    exact (Nat.card_congr e.toEquiv).symm ▸ hpK
  have hEvL : Even n := s136a_even_of_isPowTwo hn (s13_two_le_of_isL2 hLs)
  have hEvK : Even m := s136a_even_of_isPowTwo hm (s13_two_le_of_isL2 hKs)
  by_cases hpn : p ∣ 2 ^ n - 1
  · have hstr := s136a_stronglyEmbedded_three c.thin c.s13 c.sg c.r76 c.r614 hp h3 hL hK
      hne hpK hLs hKs hEvL hpn hSp
    have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hstr
    exact (s136a_false_of_two_members_of_k_eq_one c.thin c.s13 c.r1 hk hL hK hne
      (c.shape L hL) (c.shape K hK)).elim
  · by_cases hpm : p ∣ 2 ^ m - 1
    · have hstr := s136a_stronglyEmbedded_three c.thin c.s13 c.sg c.r76 c.r614 hp h3 hK hL
        hne.symm hpL hKs hLs hEvK hpm hSp
      have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hstr
      exact (s136a_false_of_two_members_of_k_eq_one c.thin c.s13 c.r1 hk hL hK hne
        (c.shape L hL) (c.shape K hK)).elim
    · have hpn' : p ∣ 2 ^ n + 1 :=
        (uc22s2121e3_dvd_of_isL2 hLs hpp hp2 hcardL).resolve_left hpn
      have hpm' : p ∣ 2 ^ m + 1 :=
        (uc22s2121e3_dvd_of_isL2 hKs hpp hp2 hcardK).resolve_left hpm
      have hnm : n = m := (InS3.k337_holds p hpp hp2 n m hn hm).2.1
        (s136a_dvd_two_pow_add_one_iff.mp hpn') (s136a_dvd_two_pow_add_one_iff.mp hpm')
      exact ⟨hnm, hpn', hSp⟩

theorem s136a_case_two
    {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (c : Ctx D V₀ V hV) {p : ℕ} (hp : p ∈ D.sig) (h3 : 3 ∉ D.sig) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : barImage D.M L ≠ barImage D.M K)
    (hpL : p ∣ Nat.card (barImage D.M L)) (hpK : p ∣ Nat.card (barImage D.M K))
    (hsum : CFSG.Open.pRank p D.M = CFSG.Open.pRank p L + CFSG.Open.pRank p K +
      CFSG.Open.pRank p (F13.Sp D.M p)) :
    ∃ n, IsPowTwo n ∧ p ∣ 2 ^ n + 1 ∧
      ((IsL2 (Bar2 L) n ∧ IsL2 (Bar2 K) n ∧ F13.Sp D.M p ≠ ⊥) ∨
        (IsU3 (Bar2 L) n ∧ IsL2 (Bar2 K) n ∧ F13.Sp D.M p = ⊥) ∨
        (IsL2 (Bar2 L) n ∧ IsU3 (Bar2 K) n ∧ F13.Sp D.M p = ⊥)) := by
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 hp
  obtain ⟨n, hn, hLs⟩ := c.shape L hL
  obtain ⟨m, hm, hKs⟩ := c.shape K hK
  rcases hLs with hL2 | hLU
  · rcases hKs with hK2 | hKU
    · obtain ⟨rfl, hpn, hSp⟩ := s136a_case_l2l2 c hp h3 hL hK hne hpL hpK hn hm hL2 hK2 hsum
      exact ⟨n, hn, hpn, Or.inl ⟨hL2, hK2, hSp⟩⟩
    · obtain ⟨k, hk, hpk, hKU', hL2', hSp⟩ :=
        s136a_case_u3 c hp hp3 hK hL hne.symm hpK hpL hm hKU (by omega)
      exact ⟨k, hk, hpk, Or.inr (Or.inr ⟨hL2', hKU', hSp⟩)⟩
  · obtain ⟨k, hk, hpk, hLU', hK2', hSp⟩ :=
      s136a_case_u3 c hp hp3 hL hK hne hpL hpK hn hLU hsum
    exact ⟨k, hk, hpk, Or.inr (Or.inl ⟨hLU', hK2', hSp⟩)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S136a

module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Milestones.LC_GL_local_rank_bounds
import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalRank

public section

namespace CFSG.RankThree.LocalRank

open CFSG.Assembly CFSG.Assembly.RankThreeEven

variable {G : Type*} [Group G] [Finite G]

theorem localRank_le_three_of_evenRank_eq_three (hrank : evenRank G = 3) {p : ℕ} (hp : p.Prime)
    (hodd : p ≠ 2) : localRank p G ≤ 3 :=
  hrank ▸ ((CFSG.Milestones.lc_gl_local_rank_bounds G).1 p hp hodd).2

theorem prime_dvd_card_of_localRank_pos {p : ℕ} (hp : p.Prime) (hpos : 0 < localRank p G) :
    p ∣ Nat.card G :=
  CFSG.RankThreeEvenClassification.Helpers.twoLocalRank_positive_prime_dvd p hp G hpos

theorem rank_three_selector_first_stratum_eq_empty (hrank : evenRank G = 3) :
    {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < localRank p G} = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun p ⟨hp, hodd, _, hlt⟩ =>
    absurd (localRank_le_three_of_evenRank_eq_three hrank hp hodd) (by omega)

theorem rank_three_selector_fourth_stratum_nonempty (hrank : evenRank G = 3) :
    {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ localRank p G = 3}.Nonempty := by
  obtain ⟨p, hp, hodd, hdvd, hle⟩ :=
    ((CFSG.Milestones.lc_gl_local_rank_bounds G).2.1 3 (by norm_num)).mpr hrank.ge
  exact ⟨p, hp, hodd, hdvd, le_antisymm (localRank_le_three_of_evenRank_eq_three hrank hp hodd) hle⟩

open _root_.Classical in
theorem sigmaA_eq_of_evenRank_eq_three (hrank : evenRank G = 3) :
    sigmaA G =
      if {p | p.Prime ∧ 5 < p ∧ localRank p G = 3}.Nonempty then
        {p | p.Prime ∧ 5 < p ∧ localRank p G = 3}
      else if {p | p.Prime ∧ 3 < p ∧ localRank p G = 3}.Nonempty then
        {p | p.Prime ∧ 3 < p ∧ localRank p G = 3}
      else {p | p.Prime ∧ p ≠ 2 ∧ localRank p G = 3} := by
  have hdvd : ∀ p, p.Prime → localRank p G = 3 → p ∣ Nat.card G := fun p hp h3 =>
    prime_dvd_card_of_localRank_pos hp (by omega)
  have h2 : {p | p.Prime ∧ 5 < p ∧ p ∣ Nat.card G ∧ localRank p G = 3} =
      {p | p.Prime ∧ 5 < p ∧ localRank p G = 3} := by
    ext p
    exact ⟨fun ⟨hp, h5, _, h3⟩ => ⟨hp, h5, h3⟩, fun ⟨hp, h5, h3⟩ => ⟨hp, h5, hdvd p hp h3, h3⟩⟩
  have h3 : {p | p.Prime ∧ 3 < p ∧ p ∣ Nat.card G ∧ localRank p G = 3} =
      {p | p.Prime ∧ 3 < p ∧ localRank p G = 3} := by
    ext p
    exact ⟨fun ⟨hp, h5, _, h3⟩ => ⟨hp, h5, h3⟩, fun ⟨hp, h5, h3⟩ => ⟨hp, h5, hdvd p hp h3, h3⟩⟩
  have h4 : {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ localRank p G = 3} =
      {p | p.Prime ∧ p ≠ 2 ∧ localRank p G = 3} := by
    ext p
    exact ⟨fun ⟨hp, h5, _, h3⟩ => ⟨hp, h5, h3⟩, fun ⟨hp, h5, h3⟩ => ⟨hp, h5, hdvd p hp h3, h3⟩⟩
  simp only [sigmaA, rank_three_selector_first_stratum_eq_empty hrank, Set.not_nonempty_empty,
    ite_false, h2, h3, h4]

theorem rank_three_selector_of_large (hrank : evenRank G = 3)
    (hT : {p | p.Prime ∧ 5 < p ∧ localRank p G = 3}.Nonempty) :
    sigmaA G = {p | p.Prime ∧ 5 < p ∧ localRank p G = 3} := by
  classical
  rw [sigmaA_eq_of_evenRank_eq_three hrank, ite_eq_left hT]

theorem rank_three_selector_of_five (hrank : evenRank G = 3)
    (hT : {p | p.Prime ∧ 5 < p ∧ localRank p G = 3} = ∅) (h5 : localRank 5 G = 3) :
    sigmaA G = {5} := by
  classical
  have hS3 : {p | p.Prime ∧ 3 < p ∧ localRank p G = 3} = {5} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, h3p, hr⟩
      by_contra hne
      have h5p : 5 < p := by rcases hp.eq_two_or_odd with h | h <;> omega
      exact Set.eq_empty_iff_forall_notMem.mp hT p ⟨hp, h5p, hr⟩
    · rintro rfl
      exact ⟨Nat.prime_five, by norm_num, h5⟩
  rw [sigmaA_eq_of_evenRank_eq_three hrank, ite_eq_right (Set.not_nonempty_iff_eq_empty.mpr hT),
    ite_eq_left (hS3 ▸ Set.singleton_nonempty 5), hS3]

theorem rank_three_selector_of_three (hrank : evenRank G = 3)
    (hT : {p | p.Prime ∧ 5 < p ∧ localRank p G = 3} = ∅) (h5 : localRank 5 G < 3) :
    sigmaA G = {3} ∧ localRank 3 G = 3 := by
  classical
  have hS3 : {p | p.Prime ∧ 3 < p ∧ localRank p G = 3} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro p ⟨hp, h3p, hr⟩
    by_cases hp5 : p = 5
    · subst hp5
      omega
    · have h5p : 5 < p := by rcases hp.eq_two_or_odd with h | h <;> omega
      exact Set.eq_empty_iff_forall_notMem.mp hT p ⟨hp, h5p, hr⟩
  have hthree : ∀ p, p.Prime → p ≠ 2 → localRank p G = 3 → p = 3 := by
    intro p hp hodd hr
    by_contra hne
    have h3p : 3 < p := by
      have := hp.two_le
      omega
    exact Set.eq_empty_iff_forall_notMem.mp hS3 p ⟨hp, h3p, hr⟩
  have hS4 : {p | p.Prime ∧ p ≠ 2 ∧ localRank p G = 3} = {3} := by
    obtain ⟨q, hq, hqodd, -, hqr⟩ := rank_three_selector_fourth_stratum_nonempty hrank
    have hq3 := hthree q hq hqodd hqr
    subst hq3
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun ⟨hp, hodd, hr⟩ => hthree p hp hodd hr, fun h => by subst h; exact ⟨hq, hqodd, hqr⟩⟩
  have hsig : sigmaA G = {3} := by
    rw [sigmaA_eq_of_evenRank_eq_three hrank, ite_eq_right (Set.not_nonempty_iff_eq_empty.mpr hT),
      ite_eq_right (Set.not_nonempty_iff_eq_empty.mpr hS3), hS4]
  refine ⟨hsig, ?_⟩
  have h3mem : 3 ∈ {p | p.Prime ∧ p ≠ 2 ∧ localRank p G = 3} := hS4 ▸ Set.mem_singleton 3
  exact h3mem.2.2

theorem rank_three_selector_localRank_eq (hrank : evenRank G = 3) {p : ℕ} (hp : p ∈ sigmaA G) :
    localRank p G = 3 := by
  classical
  rw [sigmaA_eq_of_evenRank_eq_three hrank] at hp
  split_ifs at hp
  · exact hp.2.2
  · exact hp.2.2
  · exact hp.2.2

theorem rank_three_selector_eq_three_iff (hrank : evenRank G = 3) :
    sigmaA G = {3} ↔ ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3 := by
  classical
  constructor
  · intro hsig q hq h3q
    have h3 : (3 : ℕ) ∈ sigmaA G := hsig ▸ Set.mem_singleton 3
    rw [sigmaA_eq_of_evenRank_eq_three hrank] at h3
    split_ifs at h3 with hT hS3
    · exact absurd h3.2.1 (by norm_num)
    · exact absurd h3.2.1 (by norm_num)
    · have hle := localRank_le_three_of_evenRank_eq_three hrank hq (by omega)
      by_contra hge
      exact hS3 ⟨q, hq, h3q, by omega⟩
  · intro hsmall
    have hT : {p | p.Prime ∧ 5 < p ∧ localRank p G = 3} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun p ⟨hp, h5p, hr⟩ =>
        absurd (hsmall p hp (by omega)) (by omega)
    exact (rank_three_selector_of_three hrank hT (hsmall 5 Nat.prime_five (by norm_num))).1

theorem rank_three_selector_ne_three_iff (hrank : evenRank G = 3) :
    sigmaA G ≠ {3} ↔ ∃ q : ℕ, q.Prime ∧ 3 < q ∧ localRank q G = 3 := by
  rw [Ne, rank_three_selector_eq_three_iff hrank]
  push Not
  constructor
  · rintro ⟨q, hq, h3q, hge⟩
    exact ⟨q, hq, h3q,
      le_antisymm (localRank_le_three_of_evenRank_eq_three hrank hq (by omega)) hge⟩
  · rintro ⟨q, hq, h3q, heq⟩
    exact ⟨q, hq, h3q, heq.ge⟩

theorem rank_three_selector_cases (hrank : evenRank G = 3) :
    {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ 3 < localRank p G} = ∅ ∧
    {p | p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ localRank p G = 3}.Nonempty ∧
    (∀ p ∈ sigmaA G, localRank p G = 3) ∧
    ({p | p.Prime ∧ 5 < p ∧ localRank p G = 3}.Nonempty →
      sigmaA G = {p | p.Prime ∧ 5 < p ∧ localRank p G = 3}) ∧
    ({p | p.Prime ∧ 5 < p ∧ localRank p G = 3} = ∅ → localRank 5 G = 3 → sigmaA G = {5}) ∧
    ({p | p.Prime ∧ 5 < p ∧ localRank p G = 3} = ∅ → localRank 5 G < 3 →
      sigmaA G = {3} ∧ localRank 3 G = 3) ∧
    (sigmaA G = {3} ↔ ∀ q : ℕ, q.Prime → 3 < q → localRank q G < 3) ∧
    (sigmaA G ≠ {3} ↔ ∃ q : ℕ, q.Prime ∧ 3 < q ∧ localRank q G = 3) :=
  ⟨rank_three_selector_first_stratum_eq_empty hrank,
    rank_three_selector_fourth_stratum_nonempty hrank,
    fun _ hp => rank_three_selector_localRank_eq hrank hp,
    rank_three_selector_of_large hrank, rank_three_selector_of_five hrank,
    rank_three_selector_of_three hrank, rank_three_selector_eq_three_iff hrank,
    rank_three_selector_ne_three_iff hrank⟩

end CFSG.RankThree.LocalRank

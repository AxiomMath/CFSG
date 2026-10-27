module

public import CFSG.RankThree.PartTwo.Sec16.Item167O2LocFour
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.RankThree.PartTwo.Sec13.Item135SimpleTwoRank
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProofPrime
import CFSG.RankThree.PartTwo.KFacts.KSListsProofArith
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof167Empty

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4

theorem not_small44_card_of_trialityD4
    {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 1 ≤ f)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 2 f) :
    ¬ Proof167Four.Small44 (Nat.card X) := by
  have hm : CFSG.Blueprint.TwistedChevalleyModel X .D4 (2 ^ f) := h.2
  have hcard :=
    CFSG.Timmesfeld.ExceptionalOrders.card_of_twistedChevalleyModel_D4_two hf hm
  set q := 2 ^ f with hqdef
  set n := Nat.card X with hndef
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hfac : n = q ^ 12 * ((q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1))) := by
    rw [hcard, CFSG.Open.ordTrialityD4]
    ring
  have h2dvd : 2 ^ (12 * f) ∣ n := by
    rw [hfac]
    have hq12 : q ^ 12 = 2 ^ (12 * f) := by
      rw [hqdef, ← pow_mul]
      congr 1
      omega
    rw [hq12]
    exact dvd_mul_right _ _
  rintro (⟨r, hrprime, hr3, hrn, hndvd⟩ | h5616 | h92160)
  ·
    have hrodd : Odd r := hrprime.odd_of_ne_two (by omega)
    have hr_not_dvd_q : ¬ r ∣ q := by
      intro hrd
      have hrd2 : r ∣ 2 := by
        have : r ∣ 2 ^ f := by simpa [hqdef] using hrd
        exact hrprime.dvd_of_dvd_pow this
      have hle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hrd2
      omega
    have hcop : Nat.Coprime (2 ^ (12 * f)) r :=
      Nat.Coprime.pow_left (12 * f) (Nat.coprime_two_left.mpr hrodd)
    have hd : 2 ^ (12 * f) ∣ r * (r ^ 2 - 1) := h2dvd.trans hndvd
    have hd2 : 2 ^ (12 * f) ∣ r ^ 2 - 1 := hcop.dvd_of_dvd_mul_left hd
    have hr2sub : r ^ 2 - 1 = (r - 1) * (r + 1) := by
      have h' : r ^ 2 = (r - 1) * (r + 1) + 1 := by
        obtain ⟨k, hk⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
        rw [hk]
        simp only [Nat.add_sub_cancel]
        ring
      omega
    have hd2' : 2 ^ (12 * f) ∣ (r - 1) * (r + 1) := by rwa [hr2sub] at hd2
    have h2dvd' : 2 ^ (12 * f - 1 + 1) ∣ (r - 1) * (r + 1) := by
      rwa [show 12 * f - 1 + 1 = 12 * f by omega]
    have hr_ge : 2 ^ (12 * f - 1) - 1 ≤ r := by
      have hle := Sec11.KSListsProof.two_pow_le_of_dvd_mul_succ hrodd (by omega) h2dvd'
      omega
    have hpow : 2 ^ (12 * f - 1) = q ^ 8 * 2 ^ (4 * f - 1) := by
      have hq8 : q ^ 8 = 2 ^ (8 * f) := by
        rw [hqdef, ← pow_mul]
        congr 1
        omega
      rw [hq8, ← pow_add]
      congr 1
      omega
    have h2e : 2 ≤ 2 ^ (4 * f - 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * f - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hq4ge : 16 ≤ q ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq2 4
    have hq8ge : q ^ 4 + 3 ≤ q ^ 8 := by
      calc q ^ 4 + 3 ≤ q ^ 4 + q ^ 4 := by nlinarith [hq4ge]
        _ ≤ q ^ 4 * q ^ 4 := by nlinarith [hq4ge]
        _ = q ^ 8 := by ring
    have hbig : q ^ 8 + q ^ 4 + 3 ≤ 2 ^ (12 * f - 1) := by
      rw [hpow]
      nlinarith [h2e, hq8ge]
    have hbound : q ^ 8 + q ^ 4 + 1 < 2 ^ (12 * f - 1) - 1 := by omega
    have hq6le : q ^ 6 ≤ q ^ 8 :=
      Nat.pow_le_pow_right (by omega : 0 < q) (by omega)
    have hq2le : q ^ 2 ≤ q ^ 8 :=
      Nat.pow_le_pow_right (by omega : 0 < q) (by omega)
    have hq6pos : 0 < q ^ 6 - 1 := by
      have h : 1 < q ^ 6 := Nat.one_lt_pow (by norm_num : 6 ≠ 0) (by omega : 1 < q)
      omega
    have hq2pos : 0 < q ^ 2 - 1 := by
      have h : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num : 2 ≠ 0) (by omega : 1 < q)
      omega
    have hr_not_dvd_q6 : ¬ r ∣ q ^ 6 - 1 := by
      intro hd'
      have hle := Nat.le_of_dvd hq6pos hd'
      omega
    have hr_not_dvd_q2 : ¬ r ∣ q ^ 2 - 1 := by
      intro hd'
      have hle := Nat.le_of_dvd hq2pos hd'
      omega
    have hcop' : Nat.Coprime r (q ^ 12) := by
      rw [Nat.coprime_comm]
      refine Nat.Coprime.pow_left 12 ?_
      rw [Nat.coprime_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hrprime).mpr hr_not_dvd_q
    have hrn' : r ∣ n := hrn
    rw [hfac] at hrn'
    have hr_dvd_odd : r ∣ q ^ 8 + q ^ 4 + 1 := by
      have hd' : r ∣ (q ^ 8 + q ^ 4 + 1) * ((q ^ 6 - 1) * (q ^ 2 - 1)) :=
        hcop'.dvd_of_dvd_mul_left hrn'
      rcases (hrprime.dvd_mul.mp hd') with h' | h'
      · exact h'
      rcases (hrprime.dvd_mul.mp h') with h'' | h''
      · exact absurd h'' hr_not_dvd_q6
      · exact absurd h'' hr_not_dvd_q2
    have hr_le : r ≤ q ^ 8 + q ^ 4 + 1 := Nat.le_of_dvd (by positivity) hr_dvd_odd
    omega
  ·
    have hdvd : 2 ^ (12 * f) ∣ 5616 := h2dvd.trans h5616
    have h2 : 2 ^ 12 ∣ 5616 :=
      (Nat.pow_dvd_pow 2 (by omega : 12 ≤ 12 * f)).trans hdvd
    norm_num at h2
  ·
    have hdvd : 2 ^ (12 * f) ∣ 92160 := h2dvd.trans h92160
    have hcop : Nat.Coprime (2 ^ (12 * f)) 45 :=
      Nat.Coprime.pow_left (12 * f) (by norm_num : Nat.Coprime 2 45)
    have hdvd2 : 2 ^ (12 * f) ∣ 2 ^ 11 := by
      have h45 : 92160 = 2 ^ 11 * 45 := by norm_num
      rw [h45] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
    have hle : 12 * f ≤ 11 :=
      (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
        (Nat.le_of_dvd (by positivity) hdvd2)
    omega

theorem four_le_pRank_of_isoLThreePi_two {J : Type} [Group J] [Finite J] {f : ℕ} (hf : 4 ≤ f)
    (h : Sec4.IsoLThreePi J 2 f) : 4 ≤ CFSG.pRank 2 J := by
  rcases h with ⟨h3, ⟨φ⟩⟩ | ⟨h3, ⟨φ⟩⟩
  · rw [CFSG.pRank_congr_of_mulEquiv φ 2]
    have hle := Sec17.HeadProof.two_mul_le_pRank_projSL_three (GaloisField 2 f) (p := 2)
      (k := f) (GaloisField.card 2 f (by omega))
    omega
  · have hdvd := AddSubgroup.card_addSubgroup_dvd_card (Sec13.traceQ2 f).ker
    rw [GaloisField.card 2 (2 * f) (by omega)] at hdvd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hle := Sec13.le_card_ker_traceQ2 f (by omega)
    rw [hk] at hle
    have hfk : f ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    have hr := Sec13.le_pRank_projSU_three f hk
    rw [CFSG.pRank_congr_of_mulEquiv φ 2]
    omega

theorem pRank_le_pRank_top_of_le {G : Type} [Group G] [Finite G] {L J : Subgroup G} (hLJ : L ≤ J) :
    CFSG.pRank 2 ↥L ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥J) := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 2 ↥L]
  exact CFSG.SectionRank.pRank_top_le_of_injective (by norm_num)
    (Subgroup.inclusion hLJ) (Subgroup.inclusion_injective hLJ)

theorem isQuasisimple_of_item4_4 (h44 : Sec4.Item4_4) {X : Type} [Group X] [Finite X]
    (hS4 : SectionFourHyp X) (hXp : Group.IsPerfect X)
    (hXs : IsSimpleGroup (X ⧸ aschbacherSolvableCore 3 X)) (hO2 : CFSG.pCore 2 X = ⊥)
    (hsmall : ¬ Proof167Four.Small44 (Nat.card (X ⧸ aschbacherSolvableCore 3 X)))
    (hrank : 4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup X)) : IsQuasisimple X := by
  rcases Proof167Four.isQuasisimple_or_pRank_le_three_or_small44 h44 hS4 hXp hXs hO2 with
    h | h | h
  · exact h
  · omega
  · exact absurd h hsmall

end CFSG.RankThree.PartTwo.Sec16.Proof167Empty

end

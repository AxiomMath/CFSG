module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenCase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3Case2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10CardOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_false_of_case153_1_gen (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case153_1 D V₀ V hV L) :
    False := by
  obtain ⟨hOm, hnat, -, -, hs, -⟩ := h
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 25920 := s16c167_card_isOmegaMinus_six hOm
  have hw : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hrk6 : rk ↥(⊤ : Subgroup (vStar D.M V₀ V hV L)) = 1 * 6 := by
    have := s16c1610_rk_natOmegaMinus (by norm_num) hnat
    rwa [hw] at this
  rcases hc.concl168 with h | h | h | h | h | h | h | h | h | h | h
  · have := s16c167_card_isAlt_six h.2.1
    omega
  · obtain ⟨-, ⟨L₀, -, hshape⟩, -⟩ := h
    rcases hshape with ⟨n, hn5, hn11, -, hA, -⟩ | ⟨m, hm3, hm5, -, hL, -⟩ | ⟨-, hS, -⟩ |
      ⟨-, hO, hsum⟩ | ⟨-, hO, -⟩
    · have h2 := s16c167_two_mul_card_isAlt (by omega) hA
      rw [hcard] at h2
      have : Nat.factorial n ≠ 51840 := by
        interval_cases n <;> decide
      exact this h2.symm
    · have hc' := CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_two hL
      rw [hcard] at hc'
      interval_cases m <;> revert hc' <;> decide
    · have := s16c1610_card_of_isSpn_six hS
      omega
    · have h12 := s16c1610_rk_sumOfNat_two (N := fun H U Z => NatOmegaMinus H U Z 6 1) (r := 6)
        (fun I hI => s16c1610_rk_natOmegaMinus (by norm_num) hI) hsum
      omega
    · have := s16c1610_card_of_isOmegaMinus_eight hO
      omega
  · have := h.1.2.1
    omega
  · obtain ⟨p, r, hp, -, hat, -, -⟩ := h
    rcases hp with rfl | rfl
    · have h3 := s16c167_card_isElemAbelianOfRank hat
      have hodd : Odd (3 ^ r) := Odd.pow (by decide)
      rw [← h3, hcard] at hodd
      revert hodd
      decide
    · have h3 := s16c167_card_isElemAbelianOfRank hat
      have hodd : Odd (7 ^ r) := Odd.pow (by decide)
      rw [← h3, hcard] at hodd
      revert hodd
      decide
  · have := s16c1610_card_of_isOmegaPlus_four_two h.2.1
    omega
  · have := h.2.2.1
    omega
  · have := Om8Excl.card_isL3_one h.2.1
    omega
  · have := s16c167_card_lBar_le_of_case168_8 D hc.setting.hyp151.le h
    omega
  · have := Om8Excl.card_isL3_one h.2.1
    omega
  · obtain ⟨p, -, -, -, hs2, -, -⟩ := h
    omega
  · have := h.2.2.1
    omega

private theorem s16t_mul_eq_two_gen {r s : ℕ} (hr : 0 < r) (hs : 0 < s) (h : r * s = 2) :
    (r = 1 ∧ s = 2) ∨ (r = 2 ∧ s = 1) := by
  have hr2 : r ≤ 2 := by nlinarith
  have hs2 : s ≤ 2 := by nlinarith
  interval_cases r <;> interval_cases s <;> omega

theorem s16t_false_of_case153_2_gen (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h : Case153_2 D V₀ V hV L) :
    False := by
  obtain ⟨K₀, p, hKL, hshape, hdir, hsig, -, hrs, hrs1⟩ := h
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hsmall : mSub V₀ ≤ 2 := hc.setting.hyp16.small
  have hr1 : 0 < (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard := by
    refine (Set.ncard_pos (Set.toFinite _)).2 ⟨barSub V₀ V hV K₀, 1, Subgroup.one_mem _, ?_⟩
    ext x
    simp
  have hs1 : 0 < s15 D.M V₀ V hV L := by
    refine (Set.ncard_pos (Set.toFinite _)).2 ⟨barSub V₀ V hV L, 1, Subgroup.one_mem _, ?_⟩
    ext x
    simp
  have hrs2 : (conjSet (barSub V₀ V hV K₀)
      (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard *
      s15 D.M V₀ V hV L = 2 := by
    have hpos := Nat.mul_pos hr1 hs1
    by_contra hne
    have h1 : (conjSet (barSub V₀ V hV K₀)
        (Mbar D.M V₀ V hV ⊓ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _))).ncard *
        s15 D.M V₀ V hV L = 1 := by omega
    have := hrs1 h1
    omega
  rcases hshape with ⟨rfl, -, -⟩ | ⟨rfl, hK, hnat⟩
  · rcases s16t_three_or_seven_mem_sig D hc.concl168 with h3 | h7
    · rw [hsig] at h3
      simp at h3
    · rw [hsig] at h7
      simp at h7
  · rcases s16t_mul_eq_two_gen hr1 hs1 hrs2 with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · exact hc.not_concl (Or.inr (Or.inl
        (s16t_case167_2_of_conj_one D h1217 hc.setting.hyp151 hV hKL hK hnat hdir hr hs hsig)))
    · exact s16t_false_of_two_conj D hc.concl168 hK hdir hr hs hsig

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

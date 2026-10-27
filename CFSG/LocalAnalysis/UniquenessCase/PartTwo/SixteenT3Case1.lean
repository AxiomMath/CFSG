module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3SixteenCase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10CardOm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_false_of_case153_1 (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (h : Case153_1 D ⊥ V hV L) :
    False := by
  obtain ⟨hOm, hnat, -, -, hs, -⟩ := h
  have hcard : Nat.card ↥(lBar ⊥ V hV L) = 25920 := s16c167_card_isOmegaMinus_six hOm
  have hw : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hrk6 : rk ↥(⊤ : Subgroup (vStar D.M ⊥ V hV L)) = 1 * 6 := by
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

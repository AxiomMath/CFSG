module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2MCase2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase6Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase7
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBCase11
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightV1Tr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gNine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16n9b_main_dParam_three : dParam 3 = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16n9b_main_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private theorem s16n9b_main_mem_sig {D : Data G} {p : ℕ} (h : D.sig = {p}) : p ∈ D.sig := by
  rw [h]
  exact Set.mem_singleton p

theorem s16n9b_main_sig_facts (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    {p : ℕ} (hp : p ∈ D.sig) :
    p.Prime ∧ p ≠ 2 ∧ IsStronglyPEmbedded p D.M ∧ 3 ≤ CFSG.Open.pRank p D.M :=
  ⟨(D.sig_prime p hp).1, (D.sig_prime p hp).2, hSg.sig1_sp p (h1219 ▸ hp), hSg.three_le p hp⟩

theorem s16n9b_main_of_good (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V) {p : ℕ} (hp : p ∈ D.sig)
    {N : ℕ} (hN : D.k + mSub V₀ ≤ N) (h : s16n9bGood (Mbar D.M V₀ V hV) p D.k N) :
    ((D.k + mSub V₀ : ℕ) : ℕ∞) < gammaN D.k D.M V := by
  obtain ⟨hpp, hp2, hsp, hrk⟩ := s16n9b_main_sig_facts D hSg h1219 hp
  exact lt_of_le_of_lt (Nat.cast_le.2 hN)
    (s16n9b_lt_gammaN_of_bar h16 hV hpp hp2 hsp (by omega) D.k N h)

theorem s16n9b_main_of_pRank_lt (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V₀ V : Subgroup G} (h16 : Hyp16 D V₀ V) (hV : IsElemAbelian 2 V)
    {p : ℕ} (hp : p ∈ D.sig) (hlt : CFSG.Open.pRank p (Mbar D.M V₀ V hV) < 3) :
    ((D.k + mSub V₀ : ℕ) : ℕ∞) < gammaN D.k D.M V := by
  obtain ⟨hpp, hp2, hsp, hrk⟩ := s16n9b_main_sig_facts D hSg h1219 hp
  exact s16n9b_lt_gammaN_of_pRank_lt h16 hV hpp hp2 hsp (by omega) hrk hlt D.k
    (D.k + mSub V₀)

theorem s16n9b_main_gamma (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h1217 : R1217 D) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) (hV0 : V₀ ≠ ⊥) :
    ((D.k + mSub V₀ : ℕ) : ℕ∞) < gammaN D.k D.M V := by
  have h16 : Hyp16 D V₀ V := hc.setting.hyp16
  have hLM : L ≤ D.M := hc.setting.hyp151.le
  have hm2 : mSub V₀ ≤ 2 := h16.small
  have hV1 : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV0
  rcases hc.concl168 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  ·
    exact s16n9b_main_of_pRank_lt D hSg h1219 h16 hV (s16n9b_main_mem_sig h1.2.2.2)
      (s16n9b_case1_pRank_lt D hV h1)
  ·
    have h2' : Case168_2 D V₀ V hV L := (s16e_case168_2Star_iff D V₀ V L hV hV1).1 h2
    have hσ : 3 ∈ D.sig := s16n9b_main_mem_sig h2'.2.2
    have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 hσ
    exact s16n9b_main_of_good D hSg h1219 h16 hV hσ (N := 3) (by omega)
      (s16n9bGood_of_invFix (s16c2m_case2_invFix D h1217 hV hc hV0 h2'))
  ·
    have hσ : 3 ∈ D.sig := s16n9b_main_mem_sig h3.2.2
    by_cases hge : 3 ≤ CFSG.Open.pRank 3 (Mbar D.M V₀ V hV)
    · exact s16n9b_main_of_good D hSg h1219 h16 hV hσ le_rfl
        (s16n9bGood_of_forall_fix (s16n9b_case3_fix D hV hLM h3 hge))
    · exact s16n9b_main_of_pRank_lt D hSg h1219 h16 hV hσ (by omega)
  ·
    obtain ⟨p, r, hp, hr, h4At⟩ := h4
    have hσ : p ∈ D.sig := h4At.2.2
    have hkp : D.k < dParam p := by
      rcases hp with rfl | rfl
      · have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 hσ
        rw [s16n9b_main_dParam_three]
        omega
      · have hk : D.k ≤ 2 := s16c167_k_le_two D
        rw [s16n9b_main_dParam_seven]
        omega
    by_cases hge : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV)
    · exact s16n9b_main_of_good D hSg h1219 h16 hV hσ (N := D.k + 2) (by omega)
        (s16n9b_case4_good D hV hc hp hr h4At hge hkp)
    · exact s16n9b_main_of_pRank_lt D hSg h1219 h16 hV hσ (by omega)
  ·
    have h5' : Case168_5 D V₀ V hV L := (s16e_case168_5Star_iff D V₀ V L hV hV1).1 h5
    exact s16n9b_main_of_good D hSg h1219 h16 hV (s16n9b_main_mem_sig h5'.2.2.2) le_rfl
      (s16n9b_case5_good D hV hLM h5' D.k (D.k + mSub V₀))
  ·
    have hσ : 3 ∈ D.sig := s16n9b_main_mem_sig h6.2.2.2
    have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 hσ
    exact s16n9b_main_of_good D hSg h1219 h16 hV hσ (N := 3) (by omega)
      (s16n9bGood_of_invFix (s16n9b_case6_invFix D h1217 hV hc hV0 h6))
  ·
    exact s16n9b_main_of_pRank_lt D hSg h1219 h16 hV (s16n9b_main_mem_sig h7.2.2.2)
      (s16n9b_case7_pRank_lt D hV h7)
  ·
    have h := r1613g_pRank_Mbar_le_two_of_case168_8 D hV h8
    exact s16n9b_main_of_pRank_lt D hSg h1219 h16 hV (s16n9b_main_mem_sig h8.2.2) (by omega)
  ·
    have hk : D.k ≤ 2 := s16c167_k_le_two D
    exact s16n9b_main_of_good D hSg h1219 h16 hV (s16n9b_main_mem_sig h9.2.2.2.2) (N := 4)
      (by omega) (s16n9bGood_of_invFix (s16n9b_case9_invFix D h1217 hV hc hV0 h9))
  ·
    obtain ⟨p, hp, h10At⟩ := h10
    have hσ : p ∈ D.sig := s16n9b_main_mem_sig h10At.2.2.2.1
    have hN : D.k + mSub V₀ ≤ 2 * dParam p - 1 := by
      rcases hp with rfl | rfl
      · have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 hσ
        rw [s16n9b_main_dParam_three]
        omega
      · have hk : D.k ≤ 2 := s16c167_k_le_two D
        rw [s16n9b_main_dParam_seven]
        omega
    exact s16n9b_main_of_good D hSg h1219 h16 hV hσ hN
      (s16n9bGood_of_invFix (s16n9b_case10_invFix D h1217 hV hc hV0 hp h10At))
  ·
    exact s16n9b_main_of_pRank_lt D hSg h1219 h16 hV (s16n9b_main_mem_sig h11.2.2.2)
      (s16n9b_case11_pRank_lt D h1217 hV hc hV0 h11)

theorem r16_9_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D) : R16_9 D := by
  intro V₀ V L hV hc
  have h16 : Hyp16 D V₀ V := hc.setting.hyp16
  by_cases hV0 : V₀ = ⊥
  · subst hV0
    refine ⟨⟨bot_le, fun v _ hv => ?_⟩, fun B _ => ⟨bot_le, fun v _ hv => ?_⟩⟩
    · refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
      have h1 : ⁅v, w⁆ = 1 := Subgroup.mem_bot.1 (hv w hw)
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    · refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
      have h1 : ⁅v, w⁆ = 1 := Subgroup.mem_bot.1 (hv w hw)
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
  · exact sixteen_nine_of_bounds D h16.hyp125 (s16n9b_k_add_lt_rMV D hSg h1219 hx h61 h127 h16)
      (s16n9b_main_gamma D hSg h1219 h1217 hV hc hV0)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

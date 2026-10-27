module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3BCPair
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3GapMV
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Ctx
public import Certificates.Certificate7067

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s16t_sumOfTwo_of_eq {V₀ V₁ V : Subgroup G} (hV : IsElemAbelian 2 V) (L : Subgroup G)
    (h : V₁ = V₀)
    (hs : SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6) (barSub V₁ V hV L)
      (⊤ : Subgroup (Vtil V₁ V hV)) ⊥) :
    SumOfTwoInequiv (fun H U Z => AlternatingNatural H U Z 6) (barSub V₀ V hV L)
      (⊤ : Subgroup (Vtil V₀ V hV)) ⊥ := by
  subst h
  exact hs

theorem s16t_aBar_lt_two_and_three_le_mBar_of_v1Sub_eq
    (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h1 : Case168_1 D V₀ V hV L) (hv : v1Sub D.M V₀ V hV L = V₀) :
    aBar D.M V₀ V hV < 2 ∧ 3 ≤ mBar D.M V₀ V hV := by
  obtain ⟨hMA, hL, hsum, -⟩ := h1
  exact s16t_aParam_lt_two_of_alt_pair (barSub_mono V₀ V hV hc.setting.hyp151.le) hMA hL
    (s16t_sumOfTwo_of_eq hV L hv hsum)

section Certified


theorem s16t_no_calO1_of_case168_1 (D : Data G) (hin : In10 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV)
    (h1 : Case168_1 D V₀ V hV L) (hV₀ : V₀ ≠ ⊥) (g : G) : ¬ InCalO1 D.k D.M V₀ V g := by
  intro hO1
  have h : Hyp125 D V₀ V := hc.setting.hyp16.hyp125
  obtain ⟨ha, hm⟩ := s16t_aBar_lt_two_and_three_le_mBar_of_v1Sub_eq D hc h1
    (v1Sub_of_ne_bot D.M V₀ V hV L hV₀)
  have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hin.hSg hin.h1219
    (by rw [h1.2.2.2]; exact Set.mem_singleton 3)
  have hH := s16c1610_hyp6H D hin.hx hin.h61 hin.h127 hin.h1114 h
  have hW := weakClosureSetting_of_hyp125 D hin.hx hin.h61 hin.h127 hin.h1114 h hV₀
  have h162 := hin.h162 D V₀ V hW hin.hx hin.h61 hV₀ (by omega)
  have hr : ((mSub V₀ + D.k : ℕ) : ℕ∞) < rMV D.M V := by
    refine lt_of_lt_of_le ?_ h162
    exact_mod_cast (by omega : mSub V₀ + D.k < mBar D.M V₀ V hV + mSub V₀)
  have hstar := (hH.hyp65 hV₀ hO1).inCalOStar_of_lt_rMV hr
  have h64 := hH.hyp64 hstar
  have hB := barSub_BOf_ne_bot_uncond h64
  have hβ : ((D.k + 2 : ℕ) : ℕ∞) ≤ betaN D.k D.M V := by
    have h2 := succ_le_deltaN_of_mBarGT D h ((h.mBarGT_iff_lt_mBar 2).2 (by omega)) D.k
    refine le_trans ?_ (h2.trans (deltaN_le_betaN D.k))
    rw [hk]
  have hrm : ((D.k + 2 : ℕ) : ℕ∞) ≤ rMV D.M V - (mSub V₀ : ℕ∞) := by
    have h2 : ((mBar D.M V₀ V hV : ℕ) : ℕ∞) ≤ rMV D.M V - (mSub V₀ : ℕ∞) :=
      ENat.le_sub_of_add_le_right (by exact_mod_cast ENat.coe_ne_top _) h162
    exact le_trans (by exact_mod_cast (by omega : D.k + 2 ≤ mBar D.M V₀ V hV)) h2
  have hBA := six_ten_calABar_of_ne_bot hH.hyp62 (j := 2) (by norm_num) hO1.1
    (le_min hβ hrm) hB
  have h2 : 2 ≤ aBar D.M V₀ V hV := E3.le_aParam_of_mem_aSet (by norm_num) hBA
  omega

theorem s16t_out10_of_case168_1_three (D : Data G) (hin : In10 D)
    (h1217 : R1217 D) (h153 : R15_3Small D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h1 : Case168_1 D V₀ V hV L) : Out10 D V₀ V hV := by
  have hk : D.k = 1 := Data.k_eq_one_of_three_mem D hin.hSg hin.h1219
    (by rw [h1.2.2.2]; exact Set.mem_singleton 3)
  have h1m := s16t_one_lt_mBar_of_three D h1217 h153 hc
  exact ⟨by omega, fun hV₀ g => s16t_no_calO1_of_case168_1 D hin hc h1 hV₀ g⟩

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2363a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL3Wr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpM
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen24

theorem lt_betaN_zero_of_mBarGT (D : Data G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {n : ℕ}
    (hn : MBarGT D.M V₀ V n) : (n : ℕ∞) < betaN 0 D.M V :=
  lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n)
    ((succ_le_deltaN_of_mBarGT D h hn 0).trans
      (CFSG.LocalAnalysis.WeakClosure81.deltaN_le_betaN 0))

theorem k_lt_betaN_of_case3 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h22 : R1622 D) (h61 : UC6.R6_1 D) (h127 : R127 D) (h1217 : R1217 D)
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_3 D V₀ V hV L) : (D.k : ℕ∞) < betaN 0 D.M V := by
  have h154 : Hyp154 D V₀ V L := r16_63a_holds D hSg h22 h61 h127 h1217 V₀ V L hV hS (Or.inr hc)
  have hk : D.k = 1 :=
    Data.k_eq_one_of_three_mem D hSg h1219 (by rw [hc.2.2.2]; exact Set.mem_singleton 3)
  have hβ := s15_Thirteen_beta D h1217 h154 hV hS.ne_bot
  have hγ : 2 ≤ gamma15 D.M V₀ V hV L := two_le_gamma15 D h154.hyp151 hV hS.ne_bot
  have hlt : 1 < max (gamma15 D.M V₀ V hV L)
      ((s15 D.M V₀ V hV L - 2) * gamma15 D.M V₀ V hV L) :=
    lt_of_lt_of_le (by omega) (le_max_left _ _)
  rw [hk]
  exact lt_of_lt_of_le (by exact_mod_cast hlt) hβ

theorem k_lt_betaN_of_case7 (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_7 D V₀ V hV L) : (D.k : ℕ∞) < betaN 0 D.M V :=
  lt_of_le_of_lt (by exact_mod_cast TwelveSeven.k_le_two D)
    (lt_betaN_zero_of_mBarGT D hS.setting.hyp16.hyp125 (R16_58_m_holds D V₀ V L hV hS hc))

theorem k_lt_betaN_of_case8 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h26 : R16_26 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV)
    (hc : Case167_8 D V₀ V hV L) : (D.k : ℕ∞) < betaN 0 D.M V := by
  have hk : D.k = 1 :=
    Data.k_eq_one_of_three_mem D hSg h1219 (by rw [hc.2.2.1]; exact Set.mem_singleton 3)
  rw [hk]
  exact lt_betaN_zero_of_mBarGT D hS.setting.hyp16.hyp125
    (R16_28_m_of_R16_26 D h26 V₀ V L hV hS hc)

end Sixteen24

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

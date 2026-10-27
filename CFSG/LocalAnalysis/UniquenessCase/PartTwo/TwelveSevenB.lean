module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenP
import CFSG.LocalAnalysis.WeakClosure81.NineThirteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem twelve_seven_three_one (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : IsTI V) (h8 : 8 ≤ Nat.card V)
    (hz : ∀ z ∈ D.T, (∀ t ∈ D.T, z * t = t * z) → z ≠ 1 →
      centralizer ({z} : Set G) ≤ D.M) :
    ¬ normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M := by
  intro hW1
  obtain ⟨H₀, hH₀, h124'⟩ := h124
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hyp : Hyp88 V H₀ D.T 1 :=
    { hyp7 := TwelveSeven.hyp7_of_inCalV D hV hTI h8
      calH := TwelveSeven.isCalH_of_mem_hSet D hV hH₀
      kgroup := TwelveSix.isKGroup_of_mem_hSet D hH₀
      sylow := TwelveShort.isSylowIn_of_le D (le_inf hH₀.1 (by rw [hN]; exact hTM))
      wne := TwelveFourteen.wClos_zero_ne_self hTim hcat D hV hTI (by omega)
      rank := TwelveSeven.two_lt_rk_of_card hV.2.2.2 h8
      notLe := by rw [hN]; exact hH₀.2.1
      i_le := le_rfl
      normW := inf_le_right.trans (hW1.trans hN.ge)
      centr := fun z hz' hzc hz1 => inf_le_right.trans ((hz z hz' hzc hz1).trans hN.ge) }
  obtain ⟨h1, h2⟩ := h88 hyp
  by_cases hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M
  · have h3 := h1 (TwelveSix.pRank_three_le_one D h66 hH₀ hsp) (by rw [hN]; exact hsp)
    rw [TwelveSix.hasCompFactor_calL1_iff] at h3
    exact h124'.1 h3
  · have h3 := h2 (TwelveSix.pRank_three_le_three D h66 hH₀) (fun p hp hp2 h3 => by
      rw [hN]
      exact TwelveSix.pRank_inf_le_one D h66 hH₀ hp hp2 h3)
    rw [TwelveSix.hasCompFactor_calL0_iff] at h3
    exact h124'.2 hsp h3

theorem twelve_seven_three_two (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h63 : UC6.R6_3 D) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : IsTI V) (h8 : 8 ≤ Nat.card V) (h93 : Thm93 V D.T)
    (hz : ∀ z ∈ D.T, (∀ t ∈ D.T, z * t = t * z) → z ≠ 1 →
      centralizer ({z} : Set G) ≤ D.M) :
    ∀ X : Subgroup G, ¬ F11.InP11 D X := by
  intro X hX
  have hN : normalizer (V : Set G) = D.M := normalizer_eq_of_inCalV D hV
  have h9 : Hyp9 V D.T :=
    { hyp7 := TwelveSeven.hyp7_of_inCalV D hV hTI h8
      sylow := by rw [hN]; exact TwelveShort.isSylowIn_of_le D D.sylowM.le
      ne := (TwelveFourteen.wClos_zero_ne_self hTim hcat D hV hTI (by omega)).symm
      rk_gt := TwelveSeven.two_lt_rk_of_card hV.2.2.2 h8 }
  have hXP : X ∈ calP V := TwelveSeven.mem_calP_of_inP11 D h63 hV hTI hX
  obtain ⟨p, hp, hp2, hXM, hXp, hexp, hXnc, hperm, hΓX, -⟩ := id hX
  rcases nine_thirteen h9 h93 hXP hperm with h1 | h2
  · exact twelve_seven_three_one hTim hcat D h66 h88 h124 hV hTI h8 hz (h1.trans hN.le)
  · apply twelve_seven_one hTim hcat D h86 h126 h124 hV hTI h8
    have hXU : InCalU D.M X :=
      TwelveShort.inCalU_of_inP11 D h63 hp hp2 hXM hXp hexp hΓX X le_rfl hXnc
    exact InCalU.mono D.maxLocal hXU (le_inf hXM (le_sup_left.trans h2)) inf_le_left

theorem twelve_seven (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h63 : UC6.R6_3 D) (h66 : UC6.R6_6 D)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D)
    (h124 : ∃ H₀ ∈ RankThreeUC.hSet D.T D.M, RankThreeUC.Hyp124 D.M H₀) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : IsTI V) (h8 : 8 ≤ Nat.card V) (h93 : Thm93 V D.T) :
    ¬ UniqueMax D.M (D.M ⊓ normalizer (E3.wClos V 0 D.T : Set G)) ∧
      ¬ InCalV1 D.M D.T V ∧
      ((∀ z ∈ D.T, (∀ t ∈ D.T, z * t = t * z) → z ≠ 1 → centralizer ({z} : Set G) ≤ D.M) →
        ¬ normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M ∧ ∀ X : Subgroup G, ¬ F11.InP11 D X) :=
  ⟨twelve_seven_one hTim hcat D h86 h126 h124 hV hTI h8,
    twelve_seven_two hTim hcat D h86 h126 h124 hV hTI h8,
    fun hz => ⟨twelve_seven_three_one hTim hcat D h66 h88 h124 hV hTI h8 hz,
      twelve_seven_three_two hTim hcat D h63 h66 h86 h88 h126 h124 hV hTI h8 h93 hz⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

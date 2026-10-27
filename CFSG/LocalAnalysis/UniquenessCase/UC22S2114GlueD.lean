module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K1
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L3W
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114L34
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114TitsD
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenLift
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ForceLieSmall
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218X
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21b
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114_k_eq_one_of_isU_of_r82 (hGA : GriessAllModelsStatement) {D : Data G}
    (h82 : F08.R82 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hX : IsU4 (BarInf L) 1 ∨ IsU5 (BarInf L) 1) : D.k = 1 := by
  have h := h82 L ⟨hL.1, hL.2.1, uc22s2114_three_le_pRank_of_isU hGA hL hX,
    Or.inl (PartTwo.s15_Three_qs_of_open hL.2.2)⟩
  unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
  rw [if_pos h]

theorem s21_14R_of_residuals
    (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D) (h82 : F08.R82 D)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (h3 : S21_3 D Ch) (h5 : S21_5 D Ch)
    (hR4 : S21_14R4 D Ch) (hR3U : S21_14R3U D Ch) (hR3L : S21_14R3L D Ch)
    (hD4 : S21_14D4 D Ch) (hK2 : S21_14K2 D Ch) : S21_14R D Ch := by
  intro hH c L hL hX hpow
  by_cases hL32 : IsL3 (BarInf L) 1
  · exact Or.inr (Or.inr (PartTwo.Inputs1719.lieModel_of_cover_L32 hL.2.2
      (PartTwo.TwelveThirteen.pCore_bar2_eq_bot L) (uc22p21k_barInf_equiv_of_calC hL) hL32))
  obtain ⟨t, m, f, hadm, hmod⟩ := id hX
  by_cases hl4 : 4 ≤ PartTwo.S17.CS17LieRank t m
  · exact hR4 hH c L hL hX hpow ⟨_, f, hl4, t, m, hadm, hmod, rfl⟩
  have hrk2 : ∀ {f : ℕ}, LieRankTwoEven (BarInf L) f →
      (D.k = 2 → IsPowTwo f → c.B0 ≤ normalizer (L : Set G) →
        (∀ b ∈ c.B0, CentralizesBar b L → b = 1) → 3 ≤ c.n →
        LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1 := by
    intro f hRT hk2
    have hf := hpow f hRT
    have hBL := uc22s2114_B0_le_normalizer h5 hH c hL
    have hfaith := uc22s2114_faithful h3 hH c hL (uc22s2114_not_thin hRT hf hL32)
    rcases PartTwo.s15_Thirteen_k_cases D with hk | hk
    · obtain ⟨hD, hn, hBT⟩ := uc22s2114_k1 hH c hL hRT hf hk hBL hfaith (hn3 hH c)
      exact hD4 hH c L hL hX hpow ⟨f, hD⟩ hk hn hBT hBL hfaith
    · exact hk2 hk hf hBL hfaith (hn3 hH c)
  obtain ⟨-, hf1, hadm⟩ := hadm
  cases t with
  | PSL =>
    obtain ⟨hm2, -⟩ := hadm
    simp only [PartTwo.S17.CS17LieRank] at hl4
    obtain rfl | rfl | rfl : m = 2 ∨ m = 3 ∨ m = 4 := by omega
    · exact Or.inl ⟨f, Or.inl hmod⟩
    · refine hrk2 (Or.inl hmod) fun hk hf hBL hfaith hn => ?_
      obtain ⟨hpn, h4n⟩ := uc22s2114_isPowTwo_n_of_isL3 c hL hmod hf hBL hfaith hn
      obtain ⟨e, rfl⟩ := hf
      rcases e with _ | _ | e
      · exact absurd hmod hL32
      · exact s21_14L34_holds D Ch hH c L hL hX hpow hmod hk
          (uc22s2114_n_eq_four_of_isL3_two c hL hmod hBL hfaith hpn h4n) hBL hfaith
      · exact (uc22s2114_false_of_isL3_four_three hGA hSg h614 h76 hH c hL hmod
          ⟨2 ^ e, by ring⟩ h4n).elim
    · exact hR3L hH c L hL hX hpow ⟨f, Or.inl hmod⟩
  | PSU =>
    obtain ⟨hm3, -⟩ := hadm
    simp only [PartTwo.S17.CS17LieRank] at hl4
    obtain rfl | rfl | rfl | rfl | rfl : m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
    · exact Or.inl ⟨f, Or.inr (Or.inr hmod)⟩
    · refine hrk2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod))))))
        fun hk _ hBL hfaith hn => ?_
      obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
      · have := uc22s2114_k_eq_one_of_isU_of_r82 hGA h82 hL (Or.inl hmod)
        omega
      · exact hK2 hH c L hL hX hpow (Or.inl ⟨f, hf2, Or.inr (Or.inr (Or.inl hmod))⟩) hk hn hBL
          hfaith
    · refine hrk2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmod))))))
        fun hk _ hBL hfaith hn => ?_
      obtain rfl | hf2 : f = 1 ∨ 2 ≤ f := by omega
      · have := uc22s2114_k_eq_one_of_isU_of_r82 hGA h82 hL (Or.inr hmod)
        omega
      · exact hK2 hH c L hL hX hpow (Or.inl ⟨f, hf2, Or.inr (Or.inr (Or.inr hmod))⟩) hk hn hBL
          hfaith
    · exact hR3U hH c L hL hX hpow ⟨f, Or.inl hmod⟩
    · exact hR3U hH c L hL hX hpow ⟨f, Or.inr hmod⟩
  | PSp =>
    obtain ⟨hm2, hm22⟩ := hadm
    simp only [PartTwo.S17.CS17LieRank] at hl4
    obtain rfl | rfl : m = 2 ∨ m = 3 := by omega
    · have hf2 : 2 ≤ f := by
        by_contra h
        obtain rfl : f = 1 := by omega
        exact hm22 rfl
      refine hrk2 (Or.inr (Or.inl hmod)) fun hk _ hBL hfaith hn => ?_
      exact hK2 hH c L hL hX hpow (Or.inl ⟨f, hf2, Or.inl hmod⟩) hk hn hBL hfaith
    · exact hR3L hH c L hL hX hpow ⟨f, Or.inr (Or.inl hmod)⟩
  | POmegaOdd =>
    obtain ⟨-, h2⟩ := hadm
    exact absurd rfl h2
  | POmegaPlus =>
    simp only [PartTwo.S17.CS17LieRank] at hl4
    omega
  | POmegaMinus =>
    simp only [PartTwo.S17.CS17LieRank] at hl4
    obtain rfl : m = 4 := by omega
    exact hR3L hH c L hL hX hpow ⟨f, Or.inr (Or.inr hmod)⟩
  | G2 =>
    obtain ⟨rfl, h3f⟩ := hadm
    have hf2 : 2 ≤ f := by
      by_contra h
      obtain rfl : f = 1 := by omega
      norm_num at h3f
    refine hrk2 (Or.inr (Or.inr (Or.inl hmod))) fun hk _ hBL hfaith hn => ?_
    exact hK2 hH c L hL hX hpow (Or.inl ⟨f, hf2, Or.inr (Or.inl hmod)⟩) hk hn hBL hfaith
  | F4 | E6 | E7 | E8 | twistedE6 => simp [PartTwo.S17.CS17LieRank] at hl4
  | trialityD4 =>
    subst hadm
    refine hrk2 (Or.inr (Or.inr (Or.inr (Or.inl hmod)))) fun hk _ hBL hfaith hn => ?_
    exact hK2 hH c L hL hX hpow (Or.inr ⟨f, hmod⟩) hk hn hBL hfaith
  | twistedB2 =>
    obtain ⟨rfl, -⟩ := hadm
    exact Or.inl ⟨f, Or.inr (Or.inl hmod)⟩
  | twistedG2 =>
    obtain ⟨-, h3, -⟩ := hadm
    exact absurd h3 (by norm_num)
  | twistedF4 =>
    obtain ⟨rfl, -, hodd, h3f⟩ := hadm
    obtain ⟨e, rfl⟩ := hpow f (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod)))))
    rcases e with _ | e
    · norm_num at h3f
    · rw [pow_succ] at hodd
      exact (Nat.not_odd_iff_even.2 (even_two.mul_left _) hodd).elim
  | Tits =>
    obtain ⟨rfl, -, rfl⟩ := hadm
    exact (uc22s2114_false_of_tits_three hSg h614 h76 h3 h5 hH c (hn3 hH c) hL hmod).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22

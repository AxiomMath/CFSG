module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Sz
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Orbit
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Pair
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72Build
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight72End
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.GroupTheory.PGroup.PrimePartTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R76Sig)
open CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3 (KFactSuzukiThreeFree)

theorem r872_of_inputs {G : Type} [Group G] [Finite G]
    (D : Data G) (hSz : KFactSuzukiThreeFree) (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D)
    (h76 : R76Sig D) (h870 : R870 D) : R872 D := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro L X H hc
  by_contra h3X
  have h3X0 : CFSG.Open.pRank 3 X = 0 := by omega
  obtain ⟨hcase, hXL, hXsup, hthin⟩ := hc.hyp
  have h3L : CFSG.Open.pRank 3 L = 0 := by
    have h := UC6.R869S.pRank_le_of_sup_pCore hXL hXsup Nat.prime_three (by norm_num)
    omega
  have hnd3 : ¬ 3 ∣ Nat.card L :=
    CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three h3L
  have hLM : L ≤ D.M :=
    hcase.elim (fun hL => UC22.uc22p22a_le_of_isSubnormal hL.1) (fun h => h.1)
  have hMtop : D.M ≠ ⊤ := UC22.uc22p20a_M_ne_top D
  have key : ∀ K : Subgroup G, K ∈ UC22.calC D.M → K ≤ L →
      center (Bar2 K) = ⊥ ∧ ∃ f : ℕ, CFSG.Blueprint.SuzukiModel (Bar2 K) 2 f := by
    intro K hK hKL
    have hKtop : K ≠ ⊤ := by
      intro htop
      exact hMtop (top_le_iff.mp (by simpa [htop] using hKL.trans hLM))
    have h3K : ¬ 3 ∣ Nat.card K := fun hd => hnd3 (hd.trans (Subgroup.card_dvd_of_le hKL))
    exact eight72_center_eq_bot_and_suzukiModel hSz D.standing.kProper hK hKtop h3K
  rcases hcase with hL | ⟨-, hLN, hProd⟩
  ·
    obtain ⟨-, f, hSuz⟩ := key L hL le_rfl
    exact hthin fun q hq hq2 => eight72_pRank_le_one_of_suzukiModel hSuz hq hq2
  ·
    obtain ⟨k, S, hS, hLeq⟩ := hProd
    have hpair : ∀ A ∈ List.ofFn S, ∀ B ∈ List.ofFn S, A ≤ normalizer (B : Set G) := by
      intro A hA B hB
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hB
      by_cases hij : S j = S i
      · rw [hij]
        exact Subgroup.le_normalizer
      · exact UC22.uc22p22u_calC_normalizes (hS j) (hS i) hij
    have hLsup : L = (⨆ A ∈ List.ofFn S, A : Subgroup G) := by
      apply SetLike.coe_injective
      rw [hLeq, ← UC22.uc22p22u_prod_list_eq_iSup _ hpair, List.map_ofFn]
      rfl
    have hSle : ∀ i, S i ≤ L := fun i => by
      rw [hLsup]
      exact le_iSup₂ (f := fun A (_ : A ∈ List.ofFn S) => A) (S i) (List.mem_ofFn.2 ⟨i, rfl⟩)
    by_cases hconst : ∀ i j, S i = S j
    ·
      have hLthin : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q L ≤ 1 := by
        intro q hq hq2
        by_cases hk : k = 0
        · have hLbot : L = ⊥ := by
            have h1 : (L : Set G) = ((⊥ : Subgroup G) : Set G) := by
              subst k
              rw [hLeq]
              simp [Set.singleton_one]
            exact SetLike.coe_injective h1
          have hzero : CFSG.Open.pRank q (⊥ : Subgroup G) = 0 := by
            refine le_antisymm ?_ (Nat.zero_le _)
            refine CFSG.SectionRank.pRank_le hq.one_lt (k := 0) ?_
            intro E hE _
            rw [le_bot_iff] at hE
            rw [hE, Subgroup.card_bot, pow_zero]
          rw [hLbot, hzero]
          omega
        · obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)
          have hLi₀ : L = S i₀ := by
            refine le_antisymm ?_ (hSle i₀)
            rw [hLsup]
            refine iSup₂_le fun A hA => ?_
            obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
            rw [hconst i i₀]
          obtain ⟨-, f, hSuz⟩ := key (S i₀) (hS i₀) (hSle i₀)
          rw [hLi₀]
          exact eight72_pRank_le_one_of_suzukiModel hSuz hq hq2
      exact hthin hLthin
    ·
      push Not at hconst
      obtain ⟨i, j, hne⟩ := hconst
      have h₁ : S i ∈ UC22.calC D.M := hS i
      have h₂ : S j ∈ UC22.calC D.M := hS j
      have hK₁L : S i ≤ L := hSle i
      have hK₂L : S j ≤ L := hSle j
      obtain ⟨hZ₁, f₁, hS₁⟩ := key (S i) (hS i) hK₁L
      obtain ⟨hZ₂, f₂, hS₂⟩ := key (S j) (hS j) hK₂L
      have hd₁ : 5 ∣ Nat.card (S i) :=
        (eight72_five_dvd_of_suzukiModel hS₁).trans
          (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(S i)))
      have hd₂ : 5 ∣ Nat.card (S j) :=
        (eight72_five_dvd_of_suzukiModel hS₂).trans
          (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥(S j)))
      have h2le : 2 ≤ CFSG.Open.pRank 5 (S i ⊔ S j) :=
        eight72_two_le_pRank_sup h₁ h₂ hne hZ₁ Nat.prime_five (by norm_num) hd₁ hd₂
      have h2X : 1 < CFSG.Open.pRank 5 X := by
        have hmono : CFSG.Open.pRank 5 (S i ⊔ S j) ≤ CFSG.Open.pRank 5 L :=
          CFSG.SectionRank.pRank_mono (by norm_num) (sup_le hK₁L hK₂L)
        have hLX : CFSG.Open.pRank 5 L ≤ CFSG.Open.pRank 5 X :=
          UC6.R869S.pRank_le_of_sup_pCore hXL hXsup Nat.prime_five (by norm_num)
        omega
      have hns5 := h870 L X H hc 5 Nat.prime_five (by norm_num) h2X
      have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC h₁
      have h5notsig : 5 ∉ D.sig := fun h5sig => hns5 (UC6S846.sp_of_mem_sig hSg hns h5sig)
      have h5 : CFSG.Open.pRank 5 D.M ≤ 3 := by
        by_contra h
        exact h5notsig (hSg.four_mem 5 Nat.prime_five (by norm_num) (by omega))
      obtain ⟨p, hpσ⟩ := hSg.nonempty
      obtain ⟨hpp, hp2⟩ := D.sig_prime p hpσ
      have hsp := UC6S846.sp_of_mem_sig hSg hns hpσ
      have hpL : CFSG.Open.pRank p L ≤ 1 := by
        by_contra h
        have h2 : 1 < CFSG.Open.pRank p X := by
          have h1 : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p X :=
            UC6.R869S.pRank_le_of_sup_pCore hXL hXsup hpp hp2
          omega
        exact h870 L X H hc p hpp hp2 h2 hsp
      have hp5 : p ≠ 5 := fun h => h5notsig (h ▸ hpσ)
      obtain ⟨B, hBM, hBel, hBc, hBN₁, hBN₂, ⟨V₁, hV₁, hBV₁⟩, ⟨V₂, hV₂, hBV₂⟩⟩ :=
        eight72_exists_B hSg hpσ hsp hp5 hLN hnd3 h₁ h₂ hne hK₁L hK₂L hZ₁ hZ₂ hS₁ hS₂ hpL h5
      have hRN_of : ∀ K : Subgroup G, K ∈ UC22.calC D.M → 5 ∣ Nat.card K →
          center (Bar2 K) = ⊥ →
          ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 5 R D.M →
            R ≤ normalizer (K : Set G) := by
        intro K hK h5K hZK R hR
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5 h5K
        have hxord : orderOf (x : G) = 5 := (Subgroup.orderOf_coe x).trans hx
        have hxmem : (x : G) ∈ K := x.2
        have hXcard : Nat.card (Subgroup.zpowers (x : G)) = 5 := by
          rw [Nat.card_zpowers, hxord]
        have hZ5 : ¬ 5 ∣ Nat.card (center (Bar2 K)) := by
          rw [hZK]
          simp
        intro y hy
        have hyM : y ∈ D.M := hR.le hy
        have hy5 : ∃ n : ℕ, orderOf y = 5 ^ n := by
          obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hR.isPGroup) ⟨y, hy⟩
          exact ⟨n, (Subgroup.orderOf_coe (⟨y, hy⟩ : R)).trans hn⟩
        have hy6 : Nat.Coprime (orderOf y) 6 := by
          obtain ⟨n, hn⟩ := hy5
          rw [hn]
          exact Nat.Coprime.pow_left n (by norm_num)
        exact eight72_mem_normalizer_of_coprime_six hK hyM hy6 Nat.prime_five (by norm_num)
          (Subgroup.zpowers_le.mpr hxmem) hXcard hZ5 h5
      have hRN : ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 5 R D.M →
          R ≤ normalizer (S i : Set G) ∧ R ≤ normalizer (S j : Set G) :=
        fun R hR => ⟨hRN_of (S i) h₁ hd₁ hZ₁ R hR, hRN_of (S j) h₂ hd₂ hZ₂ R hR⟩
      have hcyc₁ : ∀ S' : Sylow 5 (Bar2 (S i)), IsCyclic (S' : Subgroup (Bar2 (S i))) :=
        fun S' => eight72_sylow_isCyclic_of_suzukiModel hS₁ (by norm_num) S'
      have hcyc₂ : ∀ S' : Sylow 5 (Bar2 (S j)), IsCyclic (S' : Subgroup (Bar2 (S j))) :=
        fun S' => eight72_sylow_isCyclic_of_suzukiModel hS₂ (by norm_num) S'
      have h76p : Section7.Conclusion76 D.M p := h76 p hpσ hp2 hsp
      exact hns5 (eight72_sp_of_pair_fixed hSg h614 hpp hp2 h76p h₁ h₂ hne hZ₁
        Nat.prime_five (by norm_num) hd₁ hd₂ hcyc₁ hcyc₂ hRN hBM hBel hBc hBN₁ hBN₂
        hV₁ hV₂ hBV₁ hBV₂)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

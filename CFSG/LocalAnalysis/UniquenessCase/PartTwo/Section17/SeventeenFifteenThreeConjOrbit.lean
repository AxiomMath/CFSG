module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.WeakClosureShortcut914
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuterConj
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmallNormal914
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNAbstract
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNReduction
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNPGL27
import CFSG.GroupTheory.PerfectCoreSup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmallPermuting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.WeakClosureOrbit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_vzero_le_four_threeConj_orbit (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) (h915 : W3Lem915 G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (hG15O : Gap17_15_TOrbitFour D V₀ V)
    (hAutN : Gap17_15_autPGL2 D V₀ V L r q hC)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (h7 : IsL2Over17 (Bar2 L) 7) (hYs : ¬ IsL2Over17 (Bar2 (L ⊔ D.T)) 7)
    (hPGL : CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)))
    (hU : UniqueMax D.M (L ⊔ D.T)) : Nat.card V₀ ≤ 4 := by
  by_cases hV0 : V₀ = ⊥
  · rw [hV0]; simp
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hNM : L ⊔ D.T ≤ D.M := sup_le hLM D.sylowM.le
  have hsubN : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hC.memL.1 le_sup_left hNM
  have hLperf : L = CFSG.Quasithin.perfectCore (L ⊔ CFSG.Open.pCoreOf 2 (L ⊔ D.T)) :=
    (CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq le_sup_left hsubN hC.memL.2.1).symm
  have hNV : L ⊔ D.T ≤ normalizer (V₀ : Set G) :=
    (normalizer_eq_of_inCalV D (hyp125_inCalV hC.hyp125 hV0)) ▸ hNM
  have hpos : 0 < (conjSetOf D.T L).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨L, mem_conjSetOf_self D.T L⟩
  by_cases h1 : (conjSetOf D.T L).ncard = 1
  · have hTL : D.T ≤ normalizer (L : Set G) := le_normalizer_of_ncard_conjSetOf_eq_one h1
    have hN : (L.subgroupOf (L ⊔ D.T)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hTL)
    obtain ⟨-, A, hgrp, φ, hsurj, hker, hA⟩ := hAutN h7 hYs hN
    exact card_vzero_le_four_of_w3Lem914N7_syl hTim hcat D h66 h86 h88 h126
      (nfReduction7_holds CFSG.LocalAnalysis.WeakClosure81.nfAbstract_holds
          CFSG.LocalAnalysis.WeakClosure81.nfPGL27_holds G) starOfSylThree_holds hC.hyp125 hC.memL hN hLperf
      (exists_bar2_data le_sup_left hsubN hC.memL.2.1 hC.memL.2.2)
      ⟨A, hgrp, φ, hsurj, hker, hA⟩
      (fun P hP => mem_calP_of_isStronglyPEmbedded hC.hyp125 hV0 hsp (hP.le.trans hNM)
        hP.isPGroup) hU
  by_cases h2 : (conjSetOf D.T L).ncard = 2
  · obtain ⟨L₂, hL₂, hne, hall⟩ := exists_conj_pair_of_ncard_conjSetOf_eq_two h2
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨X, hXsyl, -⟩ := CFSG.Quasithin.exists_isSylowIn_ge 3 (H := L ⊔ D.T)
      (bot_le : (⊥ : Subgroup G) ≤ L ⊔ D.T) IsPGroup.of_bot
    have hXM : X ≤ D.M := hXsyl.le.trans hNM
    exact card_vzero_le_four_of_w3Lem915 hTim hcat D h66 h86 h88 h126 h915 hC.hyp125
      (N := L ⊔ D.T) (L := L) (L₁ := L) (L₂ := L₂) le_sup_right hNV (sup_comm ..) hLperf
      (exists_bar2_data_l3 le_sup_left hsubN hC.memL.2.1 hC.memL.2.2 h7) rfl hL₂ hne hall
      ⟨X, hXsyl,
        mem_calP_of_isStronglyPEmbedded hC.hyp125 hV0 hsp (inf_le_left.trans hXM)
          (hXsyl.isPGroup.to_le inf_le_left),
        mem_calP_of_isStronglyPEmbedded hC.hyp125 hV0 hsp (inf_le_left.trans hXM)
          (hXsyl.isPGroup.to_le inf_le_left)⟩ hU
  have hgt : 2 < (conjSetOf D.T L).ncard := by omega
  by_cases hLV : L ≤ centralizer (V₀ : Set G)
  · exact hG15O hC.hyp125 L hC.memL h7 hPGL (gap17_15_autPGL2At_of D hC h7 hPGL) hsp hU hgt hLV
  · exact card_vzero_le_four_of_not_le_centralizer hTim hcat D h86 h126 hC.hyp125 hC.memL hU hLV

theorem gap17_15_tOrbitFour_of_w3Lem914 (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) (h914 : W3Lem914 G) (V₀ V : Subgroup G) :
    Gap17_15_TOrbitFour D V₀ V := by
  intro h L hL _ _ hAut hsp hU _ _
  have hNM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hsubN : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hL.1 le_sup_left hNM
  exact card_vzero_le_four_of_w3Lem914 hTim hcat D h66 h86 h88 h126 h914 h hL
    (CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq le_sup_left hsubN hL.2.1).symm
    (exists_bar2_data le_sup_left hsubN hL.2.1 hL.2.2) hAut hsp hU


theorem gap17_15_threeConj_of_orbit (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q)
    (h82 : F08.R82 D) (h17_1 : R17_1At D V₀ V hC.hyp125)
    (h17_7 : R17_7At D V₀ V L r q hC) (h17_11 : R17_11At D V₀ V L r q hC)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h127 : R127 D) (h117 : C117 D V₀ V)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h111 : W3Thm111 G) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h915 : W3Lem915 G) (hG15O : Gap17_15_TOrbitFour D V₀ V)
    (hP : Gap17_15_P D V₀ V L r q hC)
    (hAutN : Gap17_15_autPGL2 D V₀ V L r q hC)
    (hInFSq : Gap17_15_threeConjInFSq D V₀ V L r q hC) :
    Gap17_15_threeConj D V₀ V L r q hC := by
  intro h7 hYs hgt
  obtain ⟨x, hxM, y, hyM, hxL, hyL, hyx⟩ := exists_three_conj_of_two_lt_ncard hgt
  have hk : D.k = 1 :=
    k_eq_one_of_three_conj D h82 hC.memL h7 hxM hyM hxL hyL hyx
  have hnoP : ¬ ∃ X : Subgroup G, F11.InP11 D X := by
    rintro ⟨X, hX⟩
    have hk2 : D.k = 2 := (h17_1.2 ⟨X, hX⟩).2.1
    omega
  obtain hInP | hPGL := hP h7 hk x hxM y hyM hxL hyL hyx
  · exact hnoP hInP
  have hLM : L ≤ D.M := CFSG.Quasithin.A3.subnormal_le hC.memL.1
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hNM : L ⊔ D.T ≤ D.M := sup_le hLM hTM
  have hU : UniqueMax D.M (L ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D le_sup_left hNM h17_7.1
  have hV4 : Nat.card V₀ ≤ 4 :=
    card_vzero_le_four_threeConj_orbit hTim hcat D h66 h86 h88 h126 h915 hC hG15O hAutN hsp
      h7 hYs hPGL hU
  have hm3 : 3 < mBar D.M V₀ V hC.hyp125.isElemAbelian :=
    (hC.hyp125.mBarGT_iff_lt_mBar 3).1 (h1669 hV4)
  have hL1 : barSub V₀ V hC.hyp125.isElemAbelian L ≠ ⊥ :=
    barSub_ne_bot_of_uniqueMax h127 hC.hyp125 h117 hC.memL h17_7.1
  have hb2 : bBar (UC22.conjClosure D.M L) D.M V₀ V hC.hyp125.isElemAbelian ≤ 2 :=
    SeventeenFourteen.b_le_two_of_R17_11 h17_11 hL1
  by_cases hV0 : V₀ = ⊥
  · have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
      uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
        (TwelveTwentyThree.conjClosure_le hC.memL.1.le) h17_7.1
    have h1 := twelve_twentyThree_one D hx h61 h126 h111 hC.hyp125 hV0
      hC.memL.1 hC.memL.2.2 hL1 hUc
    omega
  · let Δ : Finset (Subgroup G) := {D.T ⊔ L}
    have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
      intro H hH
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      exact ⟨le_sup_left, sup_le hTM hLM⟩
    have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
      rw [← Finset.sup_eq_iSup]
      have hsup : Δ.sup (fun H => H) = D.T ⊔ L := by simp [Δ]
      rw [hsup]
      exact uc22p22u_uniqueMax_mono D le_sup_right (sup_le hTM hLM) h17_7.1
    have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq ((fun _ => 1) H) H := by
      intro H hH
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      simpa [sup_comm] using hInFSq h7 hPGL
    have hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M →
        ¬ twoResidual H ≤ conjSubgroup D.M g := by
      intro H hH g hg
      simp only [Δ, Finset.mem_singleton] at hH
      subst hH
      exact twoResidual_not_le_conjSubgroup_of_uniqueMax D.maxLocal h17_7.1
        (CFSG.Quasithin.H13.A5.le_twoResidual_of_perfect hC.memL.2.1 le_sup_right) hg
    have hmax : Δ.sup (fun _ => 1) = 1 := by simp [Δ]
    have hmk : D.k + 1 < mBar D.M V₀ V hC.hyp125.isElemAbelian := by omega
    have hbound := twelve_twentyThree_three_two D hx h61 h66 h127 h1114 h162 hTor h1482
      h183 hC.hyp125 hV0 hC.memL.1 hC.memL.2.2 hL1 hΔ hΔU (fun _ => 1) hι hO2 hmax hmk
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

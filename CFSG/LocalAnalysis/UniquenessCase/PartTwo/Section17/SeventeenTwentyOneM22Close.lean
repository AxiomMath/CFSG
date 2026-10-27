module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22Points
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneM22Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOneBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicNineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M12SThreePairHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22HexadPairHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22TenPointThreeHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.M22ReducibleBoundHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HSRuParabolicsProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowRu

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem isSpor_bar2_of_M22 {D : Data G} {V₀ V L : Subgroup G}
    (c : Ctx17_17 D V₀ V L) (hspor : IsSpor (BarInf L) .M22)
    (hc : Subgroup.center (Bar2 L) = ⊥) : IsSpor (Bar2 L) .M22 := by
  obtain ⟨eInf⟩ := uc22p21k_barInf_equiv_of_center_bot c.mem_calC.2.2 hc
  obtain ⟨eM22⟩ := hspor
  exact ⟨eInf.symm.trans eM22⟩

section Certified


theorem gap17_21_irr_holds (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hRed : Inputs1719.K_M22ReducibleBound)
    (h17_1 : R17_1At D V₀ V hV) (h17_20 : R17_20At D V₀ V)
    (hK : Inputs1719.K_M22CoverNine) (hKHex : Inputs1719.K_M22HexadPair)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D) (hC117 : C117 D V₀ V) :
    Gap17_21_irr D V₀ V hV := by
  intro L c hspor
  obtain ⟨-, hN, -⟩ := h17_20 L c
  have hnt : ¬ F08.Thin8 L := by
    obtain ⟨hm3, -, -⟩ := h17_20 L c
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV c.mem_calC hnt
    · exact barSub_ne_bot_of_not_thin hV hC117 c.mem_calC hnt
  have hc : Subgroup.center (Bar2 L) = ⊥ :=
    center_bar2_eq_bot_of_M22 hV h17_1 hsp3 hK c hspor
  have hSp : IsSpor ↥(barSub V₀ V hV.isElemAbelian L) .M22 :=
    isSpor_barSub_of_M22 hV c hspor hc hL1
  have hSp2 : IsSpor (Bar2 L) .M22 := isSpor_bar2_of_M22 c hspor hc
  exact isIrrOn_barSub_of_M22 hRed hV h17_20 h869 h127 hC117 h640 hFF hx h61 h63 h1114
    h162 hTor h1482 h126 h111 h1214 hKHex hsp3 c hN hspor hSp hSp2

theorem gap17_21_M22Todd_holds (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hirr : Gap17_21_irr D V₀ V hV)
    (h17_1 : R17_1At D V₀ V hV) (h17_20 : R17_20At D V₀ V)
    (hK : Inputs1719.K_M22CoverNine) (hKHex : Inputs1719.K_M22HexadPair)
    (hrowM22 : Inputs1719.W4Thm11_1RowA .M22) (h4115 : WeakClosure81.W4Lem11_5Twelve)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V) :
    Gap17_21_M22Todd D V₀ V hV := by
  intro L c hspor
  obtain ⟨-, hN, -⟩ := h17_20 L c
  have hnt : ¬ F08.Thin8 L := by
    obtain ⟨hm3, -, -⟩ := h17_20 L c
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV c.mem_calC hnt
    · exact barSub_ne_bot_of_not_thin hV hC117 c.mem_calC hnt
  have hc : Subgroup.center (Bar2 L) = ⊥ :=
    center_bar2_eq_bot_of_M22 hV h17_1 hsp3 hK c hspor
  have hSp : IsSpor ↥(barSub V₀ V hV.isElemAbelian L) .M22 :=
    isSpor_barSub_of_M22 hV c hspor hc hL1
  have hirrL : IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥ := hirr L c hspor
  have hm : mBar D.M V₀ V hV.isElemAbelian ≤ bBar L D.M V₀ V hV.isElemAbelian + 2 :=
    mBar_le_bBar_add_two_of_M22 hV c h17_20 hKHex hspor hsp3 hx h61 h63 h127 h1114
      h162 hTor h1482 h126 h111 h869 hC117
  have hb : bBar L D.M V₀ V hV.isElemAbelian ≤ 5 :=
    bBar_le_five_of_M22 hV hrowM22 c.mem_calC.1.le hN hSp hirrL
  have hm7 : mBar D.M V₀ V hV.isElemAbelian ≤ 11 := by omega
  have hcard : Nat.card (Vtil V₀ V hV.isElemAbelian) = 2 ^ 10 :=
    card_vtil_eq_of_M22 hV h4115 c.mem_calC.1.le hN hSp hirrL hm7
  have hcent : Subgroup.centralizer (barSub V₀ V hV.isElemAbelian L :
      Set (MulAut (Vtil V₀ V hV.isElemAbelian))) = ⊥ :=
    centralizer_barSub_eq_bot_of_M22 hV hSp hcard hirrL
  exact ⟨hSp, hcard, hcent⟩

theorem gap17_21_M22Point_holds (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hirr : Gap17_21_irr D V₀ V hV)
    (h17_1 : R17_1At D V₀ V hV) (h17_20 : R17_20At D V₀ V)
    (hK : Inputs1719.K_M22CoverNine) (hKHex : Inputs1719.K_M22HexadPair)
    (hPt : Inputs1719.K_M22TenPointThree)
    (hrowM22 : Inputs1719.W4Thm11_1RowA .M22) (h4115 : WeakClosure81.W4Lem11_5Twelve)
    (hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (h127One : R127One D) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) :
    Gap17_21_M22Point D V₀ V hV := by
  intro L c hspor x hx0
  obtain ⟨-, hN, -⟩ := h17_20 L c
  obtain ⟨hSp, hcard, hcent⟩ :=
    gap17_21_M22Todd_holds D V₀ V hV hirr h17_1 h17_20 hK hKHex hrowM22 h4115
      hsp3 hx h61 h63 h127 h1114 h162 hTor h1482 h126 h111 h869 hC117 L c hspor
  have hnt : ¬ F08.Thin8 L := by
    obtain ⟨hm3, -, -⟩ := h17_20 L c
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV c.mem_calC hnt
    · exact barSub_ne_bot_of_not_thin hV hC117 c.mem_calC hnt
  have hirrL : IsIrrOn (barSub V₀ V hV.isElemAbelian L) ⊤ ⊥ := hirr L c hspor
  have hcard4 : Nat.card V₀ ≤ 4 :=
    card_vzero_le_four_of_hexad hV (gap17_21_M22HexadPair_of_K hV h17_20 hKHex)
      h61 h63 hsp3 hTim hcat h66 h88 h127One h93 c hspor
  have hH11 : F11.Hyp11 D V₀ V := Hyp125.hyp11 h127 c.hyp125
  have hsig : D.sig = {3} := by
    have hkey : ∀ p ∈ D.sig, p = 3 := by
      intro p hp
      by_contra hp3
      obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
      have hge : 2 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV.isElemAbelian) :=
        pRank_mbar_ge_two_of_mem_sig (hN := cTilde_normal_of_hyp11 hH11) hV hH11 hcard4
          hx h61 hp
      have hleAut := pRank_mbar_le_mulAut_m22 hV c.mem_calC hN hSp hcent (p := p) hpP
      have hle1 := pRank_mulAut_m22_le_one hpP hp2 hp3
      omega
    obtain ⟨p, hp⟩ := hx.sig_nonempty
    have hp3 : p = 3 := hkey p hp
    subst hp3
    ext q
    constructor
    · intro hq
      exact hkey q hq
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      exact hp
  have hbar3 : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV.isElemAbelian) ≤ 2 := by
    have h := pRank_mbar_le_mulAut_m22 hV c.mem_calC hN hSp hcent (p := 3) Nat.prime_three
    exact h.trans pRank_three_mulAut_m22_le
  have hc : Subgroup.center (Bar2 L) = ⊥ :=
    center_bar2_eq_bot_of_M22 hV h17_1 hsp3 hK c hspor
  have hpt : ∀ w : Vtil V₀ V hV.isElemAbelian, w ≠ 1 →
      ∃ g ∈ barSub V₀ V hV.isElemAbelian L, orderOf g = 3 ∧ g w = w :=
    exists_order_three_fix_of_M22 hV hcard hSp hirrL hPt
  exact one_lt_pRank_cElt_of_M22 hV hx h61 h127 c hN hcard4 hsig hbar3 hc hL1 hpt x hx0

theorem seventeen_twentyone_of_M22K
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h17_20 : R17_20At D V₀ V)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (h4128 : W4Lem12_8) (h119 : Inputs1719.W4Lem11_9)
    (hrowM22 : Inputs1719.W4Thm11_1RowA .M22) (hrowHS : Inputs1719.W4Thm11_1RowM .HS)
    (h4115 : WeakClosure81.W4Lem11_5Twelve)
    (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg) (h1214 : F12.R1214 D)
    (h127One : R127One D) (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h618 : W3_6_18 G) (h86 : W3Lem86_1 G)
    (h183 : W3Thm183 G) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h416 : Inputs1719.W4Lem4_16) (h77 : Inputs1719.W4Lem7_7) :
    R17_21At D V₀ V := by
  have hKS5 : Inputs1719.K_SporadicNine := Inputs1719.k_SporadicNine_holds
  have hKS6 : Inputs1719.K_M12SThreePair := Inputs1719.k_M12SThreePair_holds
  have hKC : Inputs1719.K_M22CoverNine := Inputs1719.k_M22CoverNine_holds
  have hPt : Inputs1719.K_M22TenPointThree := Inputs1719.k_M22TenPointThree_holds
  have hKHex : Inputs1719.K_M22HexadPair := Inputs1719.k_M22HexadPair_holds
  have hRed : Inputs1719.K_M22ReducibleBound := Inputs1719.k_M22ReducibleBound_holds
  have hKS7 : Inputs1719.K_HSRuParabolics := Inputs1719.k_HSRuParabolics_holds
  have h17_4 : R17_4AtA D V₀ V hV :=
    r17_4AtA_holds D h111 h126 h127 h618 hTim hcat h66 h88 h86 hx h61 h1114 h162 hTor h1482
      h183 hV h93 h1669 (Inputs1719.w4Lem4_16b_of_w4Lem4_16 h416) h77
  intro L c
  by_cases hk2 : D.k = 2
  · exact hk2
  · have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
      by_contra h
      exact hk2 ((Data.k_eq_two_iff D).2 h)
    have hirr : Gap17_21_irr D V₀ V hV :=
      gap17_21_irr_holds D V₀ V hV hRed h17_1 h17_20 hKC hKHex h640 hFF hsp3 hx h61 h63
        h127 h1114 h162 hTor h1482 h126 h111 h1214 h869 hC117
    exact seventeen_twentyone_of_M22Module D V₀ V hV h17_1 h17_4 h17_20 h869 hC117 hKS5
      hx h61 h63 h127 h1114 h162 hTor h1482 h126 h111
      (b17_21Bound_holds D V₀ V hV hx h61 h127 h1214 h4128 h869 hC117 h640 hFF h77 h119
        hrowHS Inputs1719.w4Thm11_1Row_Ru_holds) hKS6 hKS7 hirr
      (gap17_21_M22Todd_holds D V₀ V hV hirr h17_1 h17_20 hKC hKHex hrowM22 h4115
        hsp3 hx h61 h63 h127 h1114 h162 hTor h1482 h126 h111 h869 hC117)
      (gap17_21_M22Point_holds D V₀ V hV hirr h17_1 h17_20 hKC hKHex hPt hrowM22 h4115
        hsp3 hx h61 h63 h127 h1114 h162 hTor h1482 h126 h111 h869 hC117 h127One
        hTim hcat h66 h88 h93)
      hKHex h127One hsp3 hTim hcat h66 h88 h93 L c

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end

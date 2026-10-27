module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveCaseTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveU3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveU2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem one_le_of_CHasLieRank {X : Type} [Group X] {n l : ℕ}
    (h : CHasLieRank X l n) : 1 ≤ l := by
  obtain ⟨t, m, hadm, -, hrank⟩ := h
  rw [← hrank]
  rcases t <;> simp [CS17LieRank, StatedLieAdmissible] at hadm ⊢ <;> omega

theorem exists_prime_order_le_of_isL2_or_isSz {L : Subgroup G} {n r : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hr : r.Prime)
    (hrdvd : r ∣ 2 ^ n - 1) :
    ∃ A : Subgroup G, A ≤ L ∧ Nat.card A = r := by
  classical
  have hcardBar : r ∣ Nat.card (Bar2 L) := by
    rcases hshape with hL2 | hSz
    · rw [card_of_isL2 hL2]
      have hfactor : 2 ^ (2 * n) - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
        have h2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
        have h := Nat.sq_sub_sq (2 ^ n) 1
        rw [show (1 : ℕ) ^ 2 = 1 by norm_num] at h
        rw [h2, h]
        ring
      have hdvd : 2 ^ n - 1 ∣ 2 ^ (2 * n) - 1 := by
        rw [hfactor]
        exact dvd_mul_right _ _
      exact (hrdvd.trans hdvd).trans (dvd_mul_left _ _)
    · rw [CFSG.Quasithin.card_of_isSz (CFSG.Blueprint.LieModel.suzukiModel hSz).2]
      exact dvd_mul_of_dvd_right hrdvd (((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2)
  have hcard : Nat.card ↥L = Nat.card (Bar2 L) * Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
  have hdvdL : r ∣ Nat.card ↥L := by
    rw [hcard]
    exact dvd_mul_of_dvd_left hcardBar _
  obtain ⟨x, hx⟩ := @exists_prime_orderOf_dvd_card' ↥L _ _ r ⟨hr⟩ hdvdL
  refine ⟨Subgroup.zpowers (x : G), ?_, ?_⟩
  · intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact L.zpow_mem x.2 k
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

section Certified

theorem seventeen_fortyfive (D : Data G) (V₀ V : Subgroup G)
    (h1 : ∀ hV : Hyp125 D V₀ V, R17_1At D V₀ V hV)
    (h44_1 : R17_44_1AtB D V₀ V) (h44_2 : R17_44_2AtB D V₀ V)
    (h44_3 : R17_44_3AtB D V₀ V) (h899 : F08.R899 D)
    (h8100R : evenRank G ≠ 3 → F08.R8100R D) (h614 : UC6.R6_14 D)
    (hE3 : evenRank G = 3 → F07.R77E2 D ∧ R847E3ThinNN D)
    (h13 : SigmaRankThree13 D) (hSg : UC6S846.SigmaStd D)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34)
    (hK4 : Inputs1719.K_CartanRankLeThree)
    (hN : uc22p20rNativeGriess) (hK15 : Inputs1719.K_L2SzPairOuterRank)
    (h33_2 : R17_33_2 D) (h33_3 : ∀ _hV : Hyp125 D V₀ V, R17_33_3At D V₀ V)
    (h846 : F08.R846 D)
    (hBorel : Gap17_45_BorelDataCtx D) (hPRan : Gap17_45_PRanCtxAt D V₀ V)
    (hKG : CFSG.Open.IsKGroup ↥D.M)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (h93 : Thm93 V₀ D.T)
    (h147 : Inputs1719.UC2_14_7Three D)
    (hg5 : Gap17_45_UniqueMaxFive D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h126 : R126 D) (h86 : W3Lem86_1 G)
    (h111 : W3Thm111 G) (h61 : UC6.R6_1 D)
    (hx : DataExt D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D) (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) (hW4a : Inputs1719.W4Lem14_6aSmall) : R17_45At D V₀ V := by
  intro L X p n l C Dc Gamma ctx
  have hge : 1 ≤ l := one_le_of_CHasLieRank ctx.rank
  by_contra hgt
  have hl : l = 1 := by omega
  have hU3 : ¬ IsU3 (BarInf L) n :=
    fun hU3 => s17_45_su3_false ctx hU3 hN (h1 ctx.hyp125)
      (h33_2 V₀ V ctx.hyp125) (h33_3 ctx.hyp125) h846 hK3
  obtain ⟨hshape, x, hxM, hXsup, hXne⟩ :=
    s17_45_pair ctx hl hU3 hN hK4 hK3 h44_1 h44_2 h44_3 h899
  have hpair : ∃ x ∈ D.M, X = L ⊔ conjSubgroup L x ∧ X ≠ L := ⟨x, hxM, hXsup, hXne⟩
  obtain ⟨r, hr, hrdvd, hnotStrong⟩ :=
    s17_45_exists_not_strongly ctx hshape hpair (h1 ctx.hyp125) hK3 hK4
  by_cases he : evenRank G = 3
  · obtain ⟨h77, hNN⟩ := hE3 he
    exact ctx.counter (Or.inr (Or.inl (s17_45_case_two ctx.mem_calC hxM hXsup hXne ctx.X_eq
      hshape hr hrdvd ctx.p_mem hnotStrong he h13 hSg h77 h614 hNN hK15)))
  obtain ⟨A₀, hA₀L, hA₀card⟩ := exists_prime_order_le_of_isL2_or_isSz hshape hr hrdvd
  have h8100 : F08.Hyp8100 D ![L, conjSubgroup L x] ![n, n] r p A₀ X :=
    s17_45_hyp8100 ctx.mem_calC hxM hXsup hXne ctx.X_eq hshape hr hrdvd ctx.p_mem hA₀L hA₀card
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC ctx.mem_calC
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    hSg.sig1_sp p (UC6S846.sig_subset_sig1 hSg hns ctx.p_mem)
  rcases h8100R he ![L, conjSubgroup L x] ![n, n] r p A₀ X h8100 with hstr | h2 | h3 | h4
  · exact hnotStrong hstr
  · exact absurd h2.2.1 he
  · have hdata' : Gap17_45_BorelData D X p r :=
      hBorel V₀ V L X p n l r C Dc Gamma x A₀ ctx h8100 (Or.inl h3)
    obtain ⟨A, y, hAsyl, hAT, hy, hBcard, hBM, hBT, hAB, hANT⟩ :=
      s17_45_b_exists ctx h8100 (Or.inl h3)
        (hPRan L X p n l r C Dc Gamma x A₀ ctx h8100 (Or.inl h3)).1
        (gap17_45_orderP D hx hPRan L X p n l r C Dc Gamma x A₀ ctx h8100 (Or.inl h3))
        hKG hKF hdata'
    have hInFAB : Gap17_45_InFSq A (Subgroup.zpowers y) D.T :=
      gap17_45_inFSqAB (gap17_45_abtStructure_holds D) ctx h8100 (Or.inl h3)
        hAsyl hAT hy hAB hANT hdata'
    exact s17_45_case34_false D h147 hTim hcat h66 h88 h126 h86 h111 h61 hx h127 h1114
      h162 hTor h1482 h183 h1214 h869 h640 hFF hW4a h1669 ctx hg5 hxM hXsup hXne h8100
      (Or.inl h3) hAsyl hAT hBM hBcard hAB hBT hsp h93 hInFAB hANT
  · have hdata' : Gap17_45_BorelData D X p r :=
      hBorel V₀ V L X p n l r C Dc Gamma x A₀ ctx h8100 (Or.inr h4)
    obtain ⟨A, y, hAsyl, hAT, hy, hBcard, hBM, hBT, hAB, hANT⟩ :=
      s17_45_b_exists ctx h8100 (Or.inr h4)
        (hPRan L X p n l r C Dc Gamma x A₀ ctx h8100 (Or.inr h4)).1
        (gap17_45_orderP D hx hPRan L X p n l r C Dc Gamma x A₀ ctx h8100 (Or.inr h4))
        hKG hKF hdata'
    have hInFAB : Gap17_45_InFSq A (Subgroup.zpowers y) D.T :=
      gap17_45_inFSqAB (gap17_45_abtStructure_holds D) ctx h8100 (Or.inr h4)
        hAsyl hAT hy hAB hANT hdata'
    exact s17_45_case34_false D h147 hTim hcat h66 h88 h126 h86 h111 h61 hx h127 h1114
      h162 hTor h1482 h183 h1214 h869 h640 hFF hW4a h1669 ctx hg5 hxM hXsup hXne h8100
      (Or.inr h4) hAsyl hAT hBM hBcard hAB hBT hsp h93 hInFAB hANT

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

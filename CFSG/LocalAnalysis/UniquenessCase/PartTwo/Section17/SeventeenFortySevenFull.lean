module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySevenB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySevenD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L3AutOThreeRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SL3TwoAutPowerMapHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortySevenGraph
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.MbarSigmaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_2.Statement
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyNineProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s17_47_false_of_inP11 {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hL3 : IsL3 (BarInf L) n) (hLX : L = X) (hn : n = 2 ∨ n = 4)
    (h1 : R17_1At D V₀ V ctx.hyp125)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D)
    (hKpow : Inputs1719.K_SL3TwoAutPowerMap) (hW4 : Inputs1719.W4Thm14_2Used)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G} (hEL : E ≤ L)
    (hEN : E ≤ normalizer ((D.T ⊓ L : Subgroup G) : Set G))
    (hEel : CFSG.Open.IsElemAbelian r E) (hE2 : 2 ≤ CFSG.Open.pRank r E)
    (hperm : Permutes E D.T) (hEP : F11.InP11 D E) : False := by
  classical
  have hL : L ∈ calC D.M := ctx.mem_calC
  have hMN : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).mp
      (uc22p21j_normal_of_conjClosure_eq hL.1.le (hLX.trans ctx.X_eq))
  have hTL : D.T ≤ normalizer (L : Set G) := D.sylowM.le.trans hMN
  obtain ⟨hV₀, hk, hm4⟩ := h1.2 ⟨E, hEP⟩
  have hSL : IsSL3 (Bar2 L) n := isSL3_of_isL3_barInf hL hL3
  have hswap : SwapsParabolics D.T L := by
    by_contra hns
    obtain ⟨T₀, hT₀T, hTT₀, hET₀, hinv⟩ := s17_47_exists_T0_of_powerMap hTL
      (s17_47_powerMap_of_not_swaps hKpow hL hTL hSL hns) hr hr2 hEL hEN hEel.2 hperm
    exact h1.1 E (inPStar_of_inP11_of_involutions (V₀ := V₀) hEP hT₀T hTT₀ hET₀ hinv)
  have hnt : ¬ F08.Thin8 L := fun hthin => by
    have h1' := hthin r hr hr2
    have h2' := CFSG.SectionRank.pRank_mono (p := r) hr.one_lt hEL
    omega
  subst hV₀
  have hV := ctx.hyp125
  have hC117 : C117 D ⊥ V := uc22p22u_c117W D h869 V (Hyp125.hyp11 h127 hV)
  have hL1 : barSub ⊥ V hV.isElemAbelian L ≠ ⊥ := barSub_ne_bot_of_not_thin hV hC117 hL hnt
  have hLbar := isSL3_barSub_of_isL3_barInf hV hL hL1 hL3
  have hswapbar := swapsParabolics_barSub_of_calC hV hL hMN hL1 hswap
  have hpf := hV.pairFacts
  have hMs : D.M ≤ stabTil ⊥ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hK : CFSG.IsKGroup ↥(Mbar D.M ⊥ V hV.isElemAbelian) :=
    CFSG.Assembly.kGroupAllSimple_of_kGroupNonab_of_catalogImp
      (fun X _ _ _ _ h => h) CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple (isKGroup_mbar D hV.isElemAbelian hMs)
  have hO2 : Inputs1719.O2Trivial (Mbar D.M ⊥ V hV.isElemAbelian) :=
    fun P hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D hV hP hN h2
  have hLY : barSub ⊥ V hV.isElemAbelian L ≤ Mbar D.M ⊥ V hV.isElemAbelian :=
    barSub_mono ⊥ V hV.isElemAbelian hL.1.le
  have hYne : Mbar D.M ⊥ V hV.isElemAbelian ≠ ⊥ := fun hbot =>
    hL1 (le_bot_iff.1 (hbot ▸ hLY))
  have hbasic := TwelveSeventeen.isBasicModule D hx h61 h127 h1214 hV hYne
  have hLn := barSub_subgroupOf_mbar_normal (V₀ := ⊥) (V := V) hV.isElemAbelian hL.1.le hMN
  have hTY : barSub ⊥ V hV.isElemAbelian D.T ≤ Mbar D.M ⊥ V hV.isElemAbelian :=
    barSub_mono ⊥ V hV.isElemAbelian D.sylowM.le
  have hTsyl := isSylowIn_barSub_sylow D hV.isElemAbelian hMs
  have hshape : IsSL3 ↥(barSub ⊥ V hV.isElemAbelian L) 2 ∨
      IsSL3 ↥(barSub ⊥ V hV.isElemAbelian L) 4 := by
    rcases hn with rfl | rfl
    · exact Or.inl hLbar
    · exact Or.inr hLbar
  have hm4' : CFSG.Quasithin.E3.mParam (Mbar D.M ⊥ V hV.isElemAbelian) = 4 := by
    unfold mBar at hm4
    exact hm4
  have hrank := hW4 (Vtil ⊥ V hV.isElemAbelian)
    (s15_Infra_vtil_sq_eq_one ⊥ V hV.isElemAbelian)
    (Mbar D.M ⊥ V hV.isElemAbelian) (barSub ⊥ V hV.isElemAbelian L) hK hO2 hbasic hLY hLn
    hshape ⟨_, hTY, hTsyl, hswapbar⟩ hm4'
  have hp := D.sig_prime p ctx.p_mem
  have h2 := two_le_pRank_mbar_of_mem_sig hV hx h61 h127 (by simp) ctx.p_mem
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h2
  have hp3 : p = 3 := by
    by_contra hne
    have hp2 := hp.1.two_le
    have hp4 : 3 < p := by have := hp.2; omega
    have h3 := hrank p hp.1 hp4
    omega
  subst hp3
  exact (Data.k_eq_two_iff D).1 hk
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hL) ctx.p_mem)

theorem seventeen_fortyseven
    {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h43 : R17_43At D V₀ V) (h44_3 : R17_44_3AtB D V₀ V)
    (hN : uc22p20rNativeGriess)
    (h638 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_38 D) (h1219 : D.sig = D.sig1)
    (h76 : F07.R76 D) (h614 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_14 D)
    (hT : CFSG.LocalAnalysis.RankThreeUC.S15.LieOddRankChev)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D)
    (hW4 : Inputs1719.W4Thm14_2Used) :
    R17_47At D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelianRankTwo :=
    Inputs1719.k_BorelTorusAbelianRankTwo_of_griess hN
  have hK4 : Inputs1719.K_CartanRankLeThree := Inputs1719.k_CartanRankLeThree_of_griess hN
  intro L X p n l C Dc Gamma ctx hL3
  have hK17 : Inputs1719.K_L3CartanThree := Inputs1719.k_L3CartanThree_holds
  have hKAut3 : K_L3AutOThreeRank := k_L3AutOThreeRank_holds
  have hKpow : Inputs1719.K_SL3TwoAutPowerMap := Inputs1719.k_SL3TwoAutPowerMap_holds
  have hLX : L = X := s17_47_L_eq_X ctx hL3 h43
    (seventeen_fortyfour_one_of_borel hV h1 hSg) h44_3 hK4 hK3 hK17 hN
  have h2n : 2 < 2 ^ n := h43 L X p n l C Dc Gamma ctx
  by_cases h4 : 2 ^ n = 4
  · have hn2 : n = 2 := Nat.pow_right_injective (le_refl 2) (by simpa using h4)
    subst hn2
    obtain ⟨h34, hZ⟩ := s17_47_isSL3Four_of_q4 ctx hLX hL3 hN
    obtain ⟨E, hEL, hEN, hEel, hE2, hperm, hEP⟩ :=
      s17_47_sl34_exists_inP11 ctx ctx.p_mem hLX h34 hZ hSg h76 h1 hK3 hK17
    exact s17_47_false_of_inP11 ctx hL3 hLX (Or.inl rfl) h1 hSg hx h61 h127 h1214 h869 hKpow
      hW4 Nat.prime_three (by norm_num) hEL hEN hEel hE2 hperm hEP
  by_cases h16 : 2 ^ n = 16
  · have hn4 : n = 4 := Nat.pow_right_injective (le_refl 2) (by simpa using h16)
    obtain ⟨E, hEL, hEN, hEel, hEcard, hperm, hEP⟩ :=
      s17_47_exists_inP11_of_large ctx hL3 hLX (by rw [h16]; norm_num) hSg h638 h1219 h76 h614
        hK3.notL34 hK4 hK17 hKAut3 hT (r := 5) (by norm_num) le_rfl
        (by rw [hn4]; norm_num)
        (by rw [h16]; norm_num)
    have hE2 : 2 ≤ CFSG.Open.pRank 5 E := by
      have h5 := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hEel
      rw [hEcard] at h5
      have h52 : CFSG.Open.pRank 5 E = 2 :=
        Nat.pow_right_injective (by norm_num : 2 ≤ 5) (by simpa using h5.symm)
      omega
    exact s17_47_false_of_inP11 ctx hL3 hLX (Or.inr hn4) h1 hSg hx h61 h127 h1214 h869 hKpow
      hW4 (by norm_num) (by norm_num) hEL hEN hEel hE2 hperm hEP
  · have h4' : 4 < 2 ^ n := by
      have hn2 : 2 ≤ n := by
        by_contra hlt
        have hlt' : n < 2 := by omega
        interval_cases n <;> norm_num at h2n
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn2
      have e : 2 ^ (2 + m) = 4 * 2 ^ m := by rw [pow_add]; norm_num
      have hpos : 0 < 2 ^ m := by positivity
      rw [e] at h4 ⊢
      omega
    exact s17_47_false_of_large ctx hL3 hLX h4' h16 h1 hSg h638 h1219 h76 h614
      hK3.notL34 hK4 hK17 hKAut3 hT

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoCartan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoRootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U4RootLineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4RootLineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2RootLineHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.G2NotJ2
import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

private theorem one_lt_of_two_lt_two_pow_main {n : ℕ} (h : 2 < 2 ^ n) : 1 < n := by
  rcases n with _ | _ | n
  · norm_num at h
  · norm_num at h
  · omega

private theorem pRank_le_eM_of_prime_main {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : CFSG.Open.pRank p M ≤ eM M := by
  unfold eM
  refine le_csSup ?_ ?_
  · refine ⟨Nat.card M, ?_⟩
    rintro n ⟨q, hq, hq2, rfl⟩
    exact CFSG.RankThreeEvenClassification.Helpers.pRank_le_card q hq M
  · exact ⟨p, hp, hp2, rfl⟩

private theorem evenRank_eq_three_of_eM_eq_three {D : Data G} {p : ℕ}
    (hDE : DataExt D) (hp : p ∈ D.sig) (heM : eM D.M = 3) : evenRank G = 3 := by
  have h3le : 3 ≤ evenRank G := D.standing.rank
  by_contra hne
  have h4 : 3 < evenRank G := by omega
  have hp4 : 4 ≤ CFSG.Open.pRank p D.M := hDE.four_le h4 p hp
  have hp3 : CFSG.Open.pRank p D.M ≤ eM D.M :=
    pRank_le_eM_of_prime_main (D.sig_prime p hp).1 (D.sig_prime p hp).2
  omega


theorem mem_uniqueSet_of_rankTwo
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma) (hLX : L = X)
    (hshape : IsU4 (Bar2 X) n ∨ IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n) (hq : 2 < 2 ^ n)
    (h52_2 : R17_52_2At D V₀ V) (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)])
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 < r) (hdvd : r ∣ 2 ^ n - 1) (hX : X = Opp r D.M)
    {E : Subgroup G} (hEX : E ≤ X) (hEel : IsElemAbelian r E)
    (hEcard : Nat.card E = r ^ 2) :
    E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := by
  classical
  have hp' : p.Prime := (D.sig_prime p ctx.p_mem).1
  have hp2 : p ≠ 2 := (D.sig_prime p ctx.p_mem).2
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC ctx.mem_calC) ctx.p_mem
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p ctx.p_mem
  have hOp : UC22.F10.OpRes p D.M = D.M := h638 p hp' hp2 (Or.inl ctx.p_mem)
  have hn : 3 ≤ n := by
    have hr7 : 7 ≤ r := by
      rcases hr.eq_two_or_odd' with h2 | hodd
      · omega
      · rcases hodd with ⟨k, hk⟩
        omega
    have hpos : 0 < 2 ^ n - 1 := by
      have h1 : 2 ≤ 2 ^ n := by omega
      omega
    have hle : r ≤ 2 ^ n - 1 := Nat.le_of_dvd hpos hdvd
    have h8 : 8 ≤ 2 ^ n := by omega
    by_contra hlt
    have hn2 : n ≤ 2 := by omega
    have hpow : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hn2
    norm_num at hpow
    omega
  have hpn : p ∣ 2 ^ n + 1 := by
    have h1 : (p : ℤ) ∣ -1 - (2 : ℤ) ^ n := hcong.dvd
    have h2 : (p : ℤ) ∣ (2 : ℤ) ^ n + 1 := by
      have h3 : (p : ℤ) ∣ -((2 : ℤ) ^ n + 1) := by
        convert h1 using 1
        ring
      exact dvd_neg.mp h3
    have h4 : (p : ℤ) ∣ ((2 ^ n + 1 : ℕ) : ℤ) := by
      push_cast
      exact h2
    exact Int.natCast_dvd_natCast.mp h4
  have hr2 : r ≠ 2 := by omega
  have hcase : CFSG.Open.pRank p X = 2 ∨ IsU4 (Bar2 X) n := by
    rcases h52_2 L X p n l C Dc Gamma ctx with h | ⟨h, -⟩
    · exact Or.inl (hLX ▸ h)
    · exact Or.inr (hLX ▸ h)
  have hZ : Subgroup.center (Bar2 X) = ⊥ :=
    Inputs1719.center_eq_bot_of_rootLineShape hq hshape
  have hOut : IsCyclic (Outer (Bar2 X)) :=
    Inputs1719.isCyclic_outer_of_rootLineShape hshape
  have hroot : ∀ E : Subgroup G, E ≤ X → IsElemAbelian r E → Nat.card E = r ^ 2 →
      ∃ B : Subgroup G, B ≤ E ∧ Nat.card B = r ∧
        (∃ Yt : Subgroup G, Yt ≤ X ⊓ Subgroup.centralizer (B : Set G) ∧
          ∃ N₀ : Subgroup ↥Yt, ∃ hN : N₀.Normal,
            @IsL2 (↥Yt ⧸ N₀) (@QuotientGroup.Quotient.group _ _ N₀ hN) n) ∧
        (IsU4 (Bar2 X) n →
          2 ≤ CFSG.Open.pRank p (X ⊓ Subgroup.centralizer (B : Set G)) ∧
          p ∣ Nat.card ↥(X ⊓ Subgroup.centralizer (E : Set G))) := by
    intro E hEX hEel hEcard
    obtain ⟨B, hBE, hBcard, ⟨Yt, hYt, N₀, hN, hL2⟩, hU4⟩ :=
      Inputs1719.exists_rootLine_lift hKU4 hKSp4 hKG2 hshape hq hr (by omega) hdvd hEX hEel
        hEcard
    exact ⟨B, hBE, hBcard, ⟨Yt, hYt, N₀, hN, hL2⟩, fun hU4' => hU4 hU4' p hp' hp2 hpn⟩
  exact mem_uniqueSet_of_rootLine h72 hK35 ctx.p_mem hsp h3 hOp hn hpn hZ hOut hr hr2 hX
    hcase hroot hEX hEel hEcard

theorem p17_42_more_of_rankTwo
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h49 : R17_49At D V₀ V) (h50 : R17_50At D V₀ V)
    (h52 : R17_52At D V₀ V) (h53 : R17_53At D V₀ V)
    (hDE : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine) :
    P17_42_more D X n := by
  have hLX : L = X := h49 L X p n l C Dc Gamma ctx
  have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
  have hshape : IsU4 (Bar2 X) n ∨ IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n :=
    (h50 L X p n l C Dc Gamma ctx).1
  have heM : eM D.M = 3 := h52.1 L X p n l C Dc Gamma ctx
  have hE3 : evenRank G = 3 := evenRank_eq_three_of_eM_eq_three hDE ctx.p_mem heM
  have hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] :=
    h52.2.2 L X p n l C Dc Gamma ctx
  refine ⟨hE3, ?_⟩
  intro r hr hr5 hdvd
  have hXopp : X = Opp r D.M := by
    rw [← hLX]
    exact h53 L X p n l C Dc Gamma ctx r hr hr5 hdvd
  refine ⟨hXopp, ?_⟩
  intro E hEX hEel hEcard
  exact mem_uniqueSet_of_rankTwo ctx hLX hshape hq h52.2.1 hcong hSg h638 h72 hK35 hKU4
    hKSp4 hKG2 hr hr5 hdvd hXopp hEX hEel hEcard

theorem concl17_42_of_ctx_rankTwo
    {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h49 : R17_49At D V₀ V) (h50 : R17_50At D V₀ V) (h51 : R17_51At D V₀ V)
    (h52 : R17_52At D V₀ V) (h53 : R17_53At D V₀ V)
    (h880 : F08.R880 D) (hDE : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (hKU4 : Inputs1719.K_U4RootLine) (hKSp4 : Inputs1719.K_Sp4RootLine)
    (hKG2 : Inputs1719.K_G2RootLine) :
    Concl17_42 D L X p := by
  have hLX : L = X := h49 L X p n l C Dc Gamma ctx
  have hq : 2 < 2 ^ n := (h50 L X p n l C Dc Gamma ctx).2
  have h1n : 1 < n := one_lt_of_two_lt_two_pow_main hq
  have hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := h52.2.2 L X p n l C Dc Gamma ctx
  have hshape : IsU4 (Bar2 X) n ∨ IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n :=
    (h50 L X p n l C Dc Gamma ctx).1
  rcases hshape with hU4 | hSp4 | hG2
  · refine Concl17_42.of_p5 ⟨n, hU4, h1n, hcong, ?_⟩
    exact p17_42_more_of_rankTwo ctx h49 h50 h52 h53 hDE hSg h638 h72 hK35 hKU4 hKSp4 hKG2
  · have hSp4orG2 : IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n := Or.inl hSp4
    have hk1 : D.k = 1 := by
      have hJ2 : ¬ IsSpor (Bar2 X) .J2 :=
        Inputs1719.not_isSpor_J2_of_isSp4 (by omega) hSp4
      have hlist : F08.List880 (Bar2 X) := by
        have hex : ∃ m : ℕ, IsSp4 (Bar2 X) m := ⟨n, hSp4⟩
        unfold F08.List880
        tauto
      exact k_eq_one_of_list880 h880 (hLX ▸ ctx.mem_calC) hlist hJ2
    have hnodd : Odd n := by
      by_contra hodd
      have heven : Even n := Nat.not_odd_iff_even.mp hodd
      have h3dvd : 3 ∣ 2 ^ n - 1 := by
        rw [CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff]
        have h2 : (2 : ZMod 3) = -1 := by decide
        rw [h2, Even.neg_one_pow heven]
      have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
        by_contra hns
        have hk2 : D.k = 2 := (Data.k_eq_two_iff D).mpr hns
        omega
      obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 C
      refine (h51 L X p n l C Dc Gamma ctx 3 Nat.prime_three h3dvd R hR) ?_
      exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le_of_le hstr
        Nat.prime_three hR.isPGroup (hR.le.trans ctx.C_le_M_of_ctx)
    refine Concl17_42.of_p4 ⟨n, hSp4orG2, h1n, hnodd, hcong, hk1, ?_⟩
    exact p17_42_more_of_rankTwo ctx h49 h50 h52 h53 hDE hSg h638 h72 hK35 hKU4 hKSp4 hKG2
  · have hSp4orG2 : IsSp4 (Bar2 X) n ∨ IsG2 (Bar2 X) n := Or.inr hG2
    have hk1 : D.k = 1 := by
      have hJ2 : ¬ IsSpor (Bar2 X) .J2 :=
        Inputs1719.not_isSpor_J2_of_isG2 (by omega) hG2
      have hlist : F08.List880 (Bar2 X) := by
        have hex : ∃ m : ℕ, F08.IsG2Der (Bar2 X) m := ⟨n, Or.inr ⟨by omega, hG2⟩⟩
        unfold F08.List880
        tauto
      exact k_eq_one_of_list880 h880 (hLX ▸ ctx.mem_calC) hlist hJ2
    have hnodd : Odd n := by
      by_contra hodd
      have heven : Even n := Nat.not_odd_iff_even.mp hodd
      have h3dvd : 3 ∣ 2 ^ n - 1 := by
        rw [CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff]
        have h2 : (2 : ZMod 3) = -1 := by decide
        rw [h2, Even.neg_one_pow heven]
      have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
        by_contra hns
        have hk2 : D.k = 2 := (Data.k_eq_two_iff D).mpr hns
        omega
      obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 C
      refine (h51 L X p n l C Dc Gamma ctx 3 Nat.prime_three h3dvd R hR) ?_
      exact CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le_of_le hstr
        Nat.prime_three hR.isPGroup (hR.le.trans ctx.C_le_M_of_ctx)
    refine Concl17_42.of_p4 ⟨n, hSp4orG2, h1n, hnodd, hcong, hk1, ?_⟩
    exact p17_42_more_of_rankTwo ctx h49 h50 h52 h53 hDE hSg h638 h72 hK35 hKU4 hKSp4 hKG2

theorem seventeen_fortytwo_of_steps {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h175 : R17_5At D V₀ V) (h1761 : R17_6_1At D V₀ V) (h1763 : R17_6_3At D V₀ V)
    (h1717 : R17_17At D V₀ V)
    (h49 : R17_49At D V₀ V) (h50 : R17_50At D V₀ V) (h51 : R17_51At D V₀ V)
    (h52 : R17_52At D V₀ V) (h53 : R17_53At D V₀ V)
    (h880 : F08.R880 D) (hDE : DataExt D)
    (hSg : UC6S846.SigmaStd D) (h638 : UC6.R6_38 D)
    (h72 : F07.R72 D) (hK35 : UCK.K35w) :
    R17_42At D V₀ V := by
  have hTCB : CFSG.RankThree.PartOne.TauCetiCatalogBridge :=
    CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge
  intro L p hL hp
  by_contra hcounter
  obtain ⟨n, hchevL⟩ :=
    exists_cIsChevOver_of_not_concl17_42 D hTCB h175 h1761 h1763 h1717 hL hcounter
  obtain ⟨C, hcartL⟩ := exists_cIsCartanOf hL
  obtain ⟨l, Dc, Gamma, ctx⟩ :=
    exists_ctx17_42 hV hL rfl hp hcounter hchevL hcartL
  exact hcounter
    (concl17_42_of_ctx_rankTwo ctx h49 h50 h51 h52 h53 h880 hDE hSg h638 h72 hK35
      Inputs1719.k_U4RootLine_holds Inputs1719.k_Sp4RootLine_holds
      Inputs1719.k_G2RootLine_holds)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

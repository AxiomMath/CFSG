module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixShape
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzFieldKFacts
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3NN
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229CongD
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DNN
import CFSG.LocalAnalysis.UniquenessCase.UC22P20v
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2DProof
import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8101UCheap
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isL2_or_isSz_bar2_conjSubgroup {L : Subgroup G} {x : G} {n : ℕ}
    (h : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) :
    IsL2 (Bar2 (CFSG.Quasithin.conjSubgroup L x)) n ∨
      IsSz (Bar2 (CFSG.Quasithin.conjSubgroup L x)) n := by
  obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
  exact h.imp (fun hL2 => LieModel.of_mulEquiv e hL2) (fun hSz => LieModel.of_mulEquiv e hSz)

theorem s17_45_hyp8100 {D : Data G} {L X : Subgroup G} {x : G} {n r p : ℕ} {A : Subgroup G}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : X = L ⊔ CFSG.Quasithin.conjSubgroup L x) (hXne : X ≠ L)
    (hXcl : X = conjClosure D.M L)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) (hp : p ∈ D.sig)
    (hAL : A ≤ L) (hAcard : Nat.card A = r) :
    F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A X := by
  have hne : conjClosure D.M L ≠ L := fun h => hXne (hXcl.trans h)
  have hXsup' : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x := hXcl ▸ hXsup
  obtain ⟨hKcal, hKne⟩ := conjSubgroup_mem_calC_and_ne hL hxM hXsup' hne
  have hLKne : L ≠ CFSG.Quasithin.conjSubgroup L x := hKne.symm
  have hshapeK :
      IsL2 (Bar2 (CFSG.Quasithin.conjSubgroup L x)) n ∨
        IsSz (Bar2 (CFSG.Quasithin.conjSubgroup L x)) n :=
    isL2_or_isSz_bar2_conjSubgroup hshape
  refine ⟨?_, ?_, ?_, hr, ?_, hp, hAcard, Or.inl hAL, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hL
    · exact hKcal
  · simpa using hLKne
  · intro i
    fin_cases i
    · exact hshape
    · exact hshapeK
  · simpa using hrdvd
  · rw [hXsup]
    exact Subgroup.coe_mul_of_right_le_normalizer_left L _
      (uc22p22u_calC_normalizes hL hKcal hLKne)
  · rw [hXcl]
    exact (uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL).2.1

theorem s17_45_inf_l_ne_bot {L K X E : Subgroup G} {n r : ℕ}
    (hXsup : X = L ⊔ K) (hKL : K ≤ normalizer (L : Set G))
    (hKshape : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n)
    (hr : r.Prime) (hr2 : r ≠ 2)
    (hEX : E ≤ X) (hEel : IsElemAbelian r E) (hEcard : Nat.card E = r ^ 2) :
    E ⊓ L ≠ ⊥ := by
  classical
  intro hbot
  have : Fact r.Prime := ⟨hr⟩
  have hLXnorm : X ≤ normalizer (L : Set G) := hXsup.symm ▸ sup_le Subgroup.le_normalizer hKL
  have : (L.subgroupOf X).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLXnorm
  have hKX : K ≤ X := hXsup.symm ▸ le_sup_right
  let f : ↥E →* ↥X ⧸ L.subgroupOf X :=
    (QuotientGroup.mk' (L.subgroupOf X)).comp (Subgroup.inclusion hEX)
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : (QuotientGroup.mk' (L.subgroupOf X)) (Subgroup.inclusion hEX y) = 1 := hy
    rw [QuotientGroup.mk'_apply] at h1
    have hyL : (y : G) ∈ L := by
      have h2 := (QuotientGroup.eq_one_iff (Subgroup.inclusion hEX y)).mp h1
      exact (Subgroup.mem_subgroupOf).mp h2
    have hmem : (y : G) ∈ E ⊓ L := ⟨y.2, hyL⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have h2 : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (↥X ⧸ L.subgroupOf X)) := by
    have h2E : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥E) := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      exact CFSG.SectionRank.le_pRank hr.one_lt le_rfl hEel (k := 2) hEcard
    exact h2E.trans (CFSG.SectionRank.pRank_top_le_of_injective hr.one_lt f hf)
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (L.subgroupOf X)).comp (Subgroup.inclusion hKX)) := by
    intro q
    obtain ⟨xx, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf X) q
    have hxX : (xx : G) ∈ (L : Set G) * (K : Set G) := by
      have h1 : (xx : G) ∈ (↑(L ⊔ K) : Set G) := hXsup.symm ▸ xx.2
      rwa [Subgroup.coe_mul_of_right_le_normalizer_left L K hKL] at h1
    obtain ⟨l, hl, k, hk, hlk⟩ := Set.mem_mul.mp hxX
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    refine (QuotientGroup.eq_iff_div_mem).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    have hdiv : (k : G) * (xx : G)⁻¹ = l⁻¹ := by rw [← hlk]; group
    simpa only [div_eq_mul_inv, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
      hdiv] using L.inv_mem hl
  have h3 : 2 ≤ CFSG.Open.pRank r K :=
    CFSG.Quasithin.H13.Ch4.T425C27.two_le_pRank_of_surjective
      ((QuotientGroup.mk' (L.subgroupOf X)).comp (Subgroup.inclusion hKX)) hsurj hr2 h2
  have hthin : F08.Thin8 K := hKshape.elim thin8_of_isL2 thin8_of_isSz
  have h1 := hthin r hr hr2
  omega

open CFSG.LocalAnalysis.RankThreeUC (uniqueSet) in
open CFSG.RankThree.PartOne (IsStronglyPEmbedded) in
private theorem s17_45_mem_uniqueSet_of_seven_le {D : Data G}
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D) (he : evenRank G = 3)
    (hN : ∀ (L : Subgroup G) (n r p : ℕ), L ∈ calC D.M → (conjSetOf D.M L).ncard = 2 →
      (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) → r.Prime → r ≠ 2 → p ∈ D.sig →
        ∀ A : Subgroup G, A ≤ L → Nat.card A = r → normalizer (A : Set G) ≤ D.M)
    {L : Subgroup G} {n r p : ℕ} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2)
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hr : r.Prime) (hr7 : 7 ≤ r) (hp : p ∈ D.sig)
    {A : Subgroup G} (hAL : A ≤ L) (hAr : Nat.card A = r) : A ∈ uniqueSet D.M := by
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have : Fact r.Prime := ⟨hr⟩
  by_cases hspr : IsStronglyPEmbedded r D.M
  · refine uc22p22r_mem_uniqueSet_of_sp D hr hspr (hAL.trans hL.1.le)
      (IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])) ?_
    rintro rfl
    rw [Subgroup.card_bot] at hAr
    exact hr.one_lt.ne hAr
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hrσ : r ∉ D.sig := fun h => hspr (UC6S846.sp_of_mem_sig hSg hns h)
  have hr2 : r ≠ 2 := by omega
  have h2 := uc22r8u2_pRank_le_two hSg h13 he hp hr hr7 hrσ
  have hNA := hN L n r p hL hc2 hLS hr hr2 hp A hAL hAr
  obtain ⟨R, E, b, hb, rfl⟩ := uc22r8u2d_exists_basis hL hK hne hset hLS hr hr2 h2 hAL hAr
  have : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  by_cases hdvd : p ∣ Nat.card (centralizer (E : Set G))
  · exact u81_mem_uniqueSet_of_dvd (UC6S846.sp_of_mem_sig hSg hns hp) hb.sylow hb.le_R
      hb.frame.elem hb.omega (zpowers_le.2 (hb.frame.mem 0)) hNA hdvd
  · exact CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega
      hb.sylow hb.le_R hb.frame.elem hb.omega
      (uc22r8u2d_normalizer_le hSg hL hK hne hset hLS hp hr hr2 hb hNA hdvd)
      (zpowers_le.2 (hb.frame.mem 0)) hNA

theorem s17_45_case_two
    {D : Data G} {L X : Subgroup G} {x : G} {n r p : ℕ}
    (hL : L ∈ calC D.M) (hxM : x ∈ D.M)
    (hXsup : X = L ⊔ CFSG.Quasithin.conjSubgroup L x) (hXne : X ≠ L)
    (hXcl : X = conjClosure D.M L)
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) (hp : p ∈ D.sig)
    (hnstr : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M)
    (he : evenRank G = 3) (h13 : SigmaRankThree13 D) (hSg : UC6S846.SigmaStd D)
    (h77 : F07.R77E2 D) (h614 : UC6.R6_14 D) (hNN : R847E3ThinNN D)
    (hK15 : Inputs1719.K_L2SzPairOuterRank) :
    P17_42_2 D L X p := by
  have hne : conjClosure D.M L ≠ L := fun h => hXne (hXcl.trans h)
  have hXsup' : conjClosure D.M L = L ⊔ CFSG.Quasithin.conjSubgroup L x := hXcl ▸ hXsup
  obtain ⟨hKcal, hKne⟩ := conjSubgroup_mem_calC_and_ne hL hxM hXsup' hne
  have hLKne : L ≠ CFSG.Quasithin.conjSubgroup L x := hKne.symm
  have hKshape := isL2_or_isSz_bar2_conjSubgroup (x := x) hshape
  have hc2 : (conjSetOf D.M L).ncard = 2 := ncard_eq_two_of_p42 hL hxM hXsup' hne
  have hn1 : 1 ≤ n := by
    rcases hshape with h | h
    · have := s13_two_le_of_isL2 h
      omega
    · have := (s13_odd_three_le_of_isSz h).2
      omega
  have hr2 : r ≠ 2 := uc22p20v_ne_two_of_dvd_sub_one hn1 hr hrdvd
  refine ⟨n, x, hxM, hXsup, hXne, ?_, ?_⟩
  · exact uc22ine229_cong_of_ncard_two hSg h77 h614 hL hc2 hshape hr hr2 hrdvd hnstr hp
  refine ⟨he, ?_⟩
  intro r' hr' hr'5 hr'dvd
  have hr'7 : 7 ≤ r' := by
    have h6 : r' ≠ 6 := by
      rintro rfl
      norm_num at hr'
    omega
  have hr'2 : r' ≠ 2 := by omega
  have h1mod : (2 : ℤ) ^ n ≡ 1 [ZMOD (r' : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have hdvdZ : (r' : ℤ) ∣ (2 : ℤ) ^ n - 1 := by
      have hcast : ((2 ^ n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ n - 1 := by
        rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow]
        norm_num
      rw [← hcast]
      exact Int.natCast_dvd_natCast.mpr hr'dvd
    simpa [neg_sub] using (dvd_neg.mpr hdvdZ)
  have hnotsig : r' ∉ D.sig := by
    intro hr'sig
    rcases uc22ine229_cong_of_ncard_two hSg h77 h614 hL hc2 hshape hr hr2 hrdvd hnstr hr'sig with
      ⟨-, hc1⟩ | ⟨-, hc1⟩
    · have h2dvd : r' ∣ 2 := by
        have h2dvdZ : (r' : ℤ) ∣ 2 := by
          have h := Int.modEq_iff_dvd.mp (hc1.symm.trans h1mod)
          simpa using h
        exact_mod_cast h2dvdZ
      rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h | h
      · exact hr'.ne_one h
      · omega
    · have hsq : (2 : ℤ) ^ (2 * n) ≡ 1 [ZMOD (r' : ℤ)] := by
        rw [mul_comm 2 n, pow_mul]
        simpa using h1mod.pow 2
      have h2dvd : r' ∣ 2 := by
        have h2dvdZ : (r' : ℤ) ∣ 2 := by
          have h := Int.modEq_iff_dvd.mp (hc1.symm.trans hsq)
          simpa using h
        exact_mod_cast h2dvdZ
      rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h | h
      · exact hr'.ne_one h
      · omega
  have hp_eq : CFSG.Open.pRank p D.M = 3 := by
    have h3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hp
    have hle : CFSG.Open.pRank p D.M ≤ 3 := by
      have h := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p
        (D.sig_prime p hp).1 (D.sig_prime p hp).2 D.M D.maxLocal.1
      rwa [he] at h
    omega
  have hle2 : CFSG.Open.pRank r' D.M ≤ 2 := by
    by_contra hcon
    have h3 : 3 ≤ CFSG.Open.pRank r' D.M := by omega
    exact hnotsig (h13 ⟨p, hp, hp_eq⟩ r' hr' hr'7 h3)
  have hXOpp : X = Opp r' D.M := by
    by_contra hne'
    have hne'' : conjClosure D.M L ≠ Opp r' D.M := fun h => hne' (hXcl.trans h)
    have h3' : 3 ≤ CFSG.pRank r' ↥D.M :=
      hK15 D.M L n r' hL hshape hne hr' hr'5 hr'dvd hne''
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup] at h3'
    omega
  refine ⟨hXOpp, ?_⟩
  intro E hEX hEel hEcard
  have hXM : X ≤ D.M :=
    hXcl ▸ (uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL).1
  have hEM : E ≤ D.M := hEX.trans hXM
  have hKLnorm : CFSG.Quasithin.conjSubgroup L x ≤ normalizer (L : Set G) :=
    uc22p22u_calC_normalizes hL hKcal hLKne
  have hnebot : E ⊓ L ≠ ⊥ :=
    s17_45_inf_l_ne_bot hXsup hKLnorm hKshape hr' hr'2 hEX hEel hEcard
  obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hnebot
  have hyE : (y : G) ∈ E := y.2.1
  have hyL : (y : G) ∈ L := y.2.2
  have hy1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
  have hA'E : Subgroup.zpowers (y : G) ≤ E := Subgroup.zpowers_le.mpr hyE
  have hA'L : Subgroup.zpowers (y : G) ≤ L := Subgroup.zpowers_le.mpr hyL
  have hA'card : Nat.card (Subgroup.zpowers (y : G)) = r' := by
    have : Fact r'.Prime := ⟨hr'⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEel.2 y hyE) hy1
  have hA'U : Subgroup.zpowers (y : G) ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M :=
    s17_45_mem_uniqueSet_of_seven_le hSg h13 he
      (normalizer_le_of_r847E3ThinNN hNN) hL hc2 hshape hr' hr'7 hp hA'L hA'card
  exact CFSG.LocalAnalysis.RankThreeUC.mem_uniqueSet_of_le hA'U hA'E hEM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

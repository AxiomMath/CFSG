module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.L34ComponentCoverFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1SchurU4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenClassicalCoverThreePart
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKJPrimeLie
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K4143Reduce
public import CFSG.LocalAnalysis.OddStandard.GlueAlt
public import CFSG.LieType.Steinberg.CentralExt.PSLCoverCenter
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_three_not_dvd_centralizer_of_component_three_rank
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q)) :
    ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let B : Subgroup (MulAut (Vtil V₀ V hV)) := lBar V₀ V hV L
  let K : Subgroup (MulAut (Vtil V₀ V hV)) := s1t3KBar A B
  let X := Bar2 D.M
  have hms : D.M ≤ stabTil V₀ V := c.m_le_stabTil
  obtain ⟨Y, hYcalC, hbarY, -⟩ :=
    exists_calC_cover_of_simple_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp
      hsimple
  obtain ⟨ψ, hψ⟩ := exists_barLift_of_hyp125 (D := D) (V₀ := V₀) (V := V) (hV := hV)
    c.setting.hyp16.hyp125
  have hrangeψ : ψ.range = A := by
    ext φ
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
      rw [hψ m]
      exact actTil_mem_barSub V₀ V hV m.2 (hms m.2)
    · intro hφ
      obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV D.M φ).1 hφ
      refine MonoidHom.mem_range.2 ⟨QuotientGroup.mk (⟨(g : G), hg⟩ : ↥D.M), ?_⟩
      rw [hψ ⟨(g : G), hg⟩]
      exact hgφ
  let C : Subgroup X := UC22.barImage D.M Y
  have hC : CFSG.IsComponent C := UC22.uc22p22l_barImage_isComponent hYcalC
  have hmap : C.map ψ = B :=
    barImage_map_eq_of_mem_calC c.setting.hyp16.hyp125 hYcalC hbarY ψ hψ
  obtain ⟨eCZ⟩ := exists_quotient_center_equiv_of_map_eq ψ hC hmap hsimple
  have hZC : ¬ 3 ∣ Nat.card (Subgroup.center ↥C) := hcover ↥C ((CFSG.Quasithin.A3.isQuasisimple_iff_open (Q := ↥C)).mp hC.1) ⟨eCZ⟩
  have h3C : 3 ≤ CFSG.Open.pRank 3 C := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup C]
    rw [← CFSG.SectionRank.pRank_quotient_eq (p := 3) (Subgroup.center ↥C) hZC]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eCZ]
    exact hrank
  obtain ⟨E, hEC, hE, hE27⟩ :=
    CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 h3C
  let H : Subgroup X := Subgroup.centralizer (C : Set X)
  have hKmap : H.map ψ = K := by
    apply le_antisymm
    · rintro k ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [← hrangeψ]
        exact MonoidHom.mem_range.2 ⟨x, rfl⟩
      · exact Subgroup.mem_centralizer_iff.mpr (by
        intro b hb
        have hbmap : b ∈ C.map ψ := by rw [hmap]; exact hb
        obtain ⟨cc, hcc, hccψ⟩ := Subgroup.mem_map.1 hbmap
        have hxc : cc * (x : X) = (x : X) * cc :=
          Subgroup.mem_centralizer_iff.1 hx cc hcc
        calc b * ψ x = ψ cc * ψ x := by rw [hccψ]
          _ = ψ (cc * (x : X)) := by rw [map_mul]
          _ = ψ ((x : X) * cc) := by rw [hxc]
          _ = ψ x * ψ cc := by rw [map_mul]
          _ = ψ x * b := by rw [hccψ])
    · intro k hk
      have hkA : k ∈ A := hk.1
      have hkcent : k ∈ Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV))) := hk.2
      have hkrange : k ∈ ψ.range := by rw [hrangeψ]; exact hkA
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hkrange
      refine Subgroup.mem_map.2 ⟨x, ?_, hx⟩
      have hxcent : ψ x ∈ Subgroup.centralizer (B : Set (MulAut (Vtil V₀ V hV))) := by
        rwa [hx]
      exact mem_centralizer_barImage_of_map_mem_centralizer c.setting.hyp16.hyp125 hYcalC hbarY
        hsimple ψ hψ hxcent
  intro h3K
  have h3map : 3 ∣ Nat.card (H.map ψ) := by rwa [hKmap]
  have h3H : 3 ∣ Nat.card ↥H := h3map.trans (Subgroup.card_map_dvd (H := H) ψ)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3H
  have hyorder : orderOf (y : X) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hy3 : (y : X) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa using congrArg Subtype.val h
  have hyE : (y : X) ∉ E := by
    intro hyEin
    have hyC : (y : X) ∈ C := hEC hyEin
    have hyZ : (⟨(y : X), hyC⟩ : ↥C) ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 y.2 (g : X) g.2)
    have hdvd : 3 ∣ Nat.card (Subgroup.center C) := by
      have ho : orderOf (⟨(y : X), hyC⟩ : ↥C) = 3 :=
        (Subgroup.orderOf_mk (y : X) hyC).trans hyorder
      exact ho ▸ Subgroup.orderOf_dvd_natCard (Subgroup.center C) hyZ
    exact hZC hdvd
  have hcomm : ∀ e ∈ E, e * (y : X) = (y : X) * e := by
    intro e he
    exact Subgroup.mem_centralizer_iff.1 y.2 e (hEC he)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K4143K2.four_le_pRank_of_commute hE hE27 hy3 hyE hcomm
  have hle : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 := by
    rw [UC22.pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)]
    calc CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
          CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
            (by norm_num) D.M D.maxLocal.1
      _ = 3 := c.std.h3
  omega

theorem s168e3_card_center_eq_one_of_isSLn_two_of_five_le
    {Q B : Type} [Group Q] [Finite Q] [Group B]
    {n : ℕ} (hn : 5 ≤ n) (hSL : IsSLn B n 1)
    (hQ : Group.IsPerfect Q)
    (eQ : (Q ⧸ Subgroup.center Q) ≃* B) :
    Nat.card (Subgroup.center Q) = 1 := by
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eSL⟩⟩ := hSL
  let : Field K := hKfield
  let : Finite K := hKfinite
  let : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨fproj⟩ := s15k_jp_projEquiv hK2 (StatedSL n K)
  let ePSL : B ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
    (eSL.trans fproj.symm).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm
  have hdvd :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.card_center_dvd_gcd_of_psl_of_five_le
      hQ hn (eQ.trans ePSL)
  have hKsub : Nat.card K - 1 = 1 := by omega
  have hdvd1 : Nat.card (Subgroup.center Q) ∣ 1 := by
    rw [hKsub] at hdvd
    simpa only [Nat.gcd_one_right] using hdvd
  exact Nat.dvd_one.mp hdvd1

theorem cover_center_three_free_of_isSLn {X : Type} [Group X] {n : ℕ} (hn : 5 ≤ n)
    (h : IsSLn X n 1) :
    ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* X) → ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  intro Q _ _ hQ ⟨eQ⟩
  have hZ1 : Nat.card (Subgroup.center Q) = 1 :=
    s168e3_card_center_eq_one_of_isSLn_two_of_five_le hn h (Group.IsPerfect.mk hQ.1) eQ
  rw [hZ1]
  norm_num

theorem s168e3_three_not_dvd_kBar_of_sl_six_seven
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) n 1) :
    ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn5 : 5 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hn6 : 6 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_ln (s16k_isLn_of_isSLn hn3 hSL)
  have hcover := cover_center_three_free_of_isSLn hn5 hSL
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eSL⟩⟩ := hSL
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [Fintype.card_eq_nat_card, hK2])
  obtain ⟨fproj⟩ := s15k_jp_projEquiv hK2 (StatedSL n K)
  let eProj : ↥(lBar V₀ V hV L) ≃* StatedProj (StatedSL n K) := eSL.trans fproj.symm
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eProj]
    exact CFSG.SectionRank.ClassicalEven.psl_three_le_pRank_three (K := K) (n := n) hn6
  exact s168e3_three_not_dvd_centralizer_of_component_three_rank c hcomp hsimple hrank hcover

theorem s168e3_three_not_dvd_kBar_of_sp_six
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1) :
    ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := s16c167_cfg2_simple_sp hSp
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨eSp⟩⟩ := hSp
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [Fintype.card_eq_nat_card, hK2])
  have hSp3 : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 K) := by simpa using eSp
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) hSp3]
    exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedSp
      (K := K) (n := 3) (r := 3) Nat.prime_three (by rw [hK2]; norm_num)
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    haveI : Group.IsPerfect Q := ⟨hQ.1⟩
    exact s16lc_sp_center_three_free (F := K) (m := 3) (by norm_num) (Q := Q)
      (e := eQ.trans hSp3)
  exact s168e3_three_not_dvd_centralizer_of_component_three_rank c hcomp hsimple hrank hcover

theorem s168e3_three_not_dvd_kBar_of_omega_minus_eight
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1) :
    ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_omegaMinus_eight hOm
  obtain ⟨-, K, hKfield, hKfinite, b, c₀, hKcard, hirr, ⟨eOm⟩⟩ := hOm
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [Fintype.card_eq_nat_card, hK2])
  have hOm4 : ↥(lBar V₀ V hV L) ≃*
      StatedProj (StatedOmega (StatedQuadMinus 4 K b c₀)) := by simpa using eOm
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) hOm4]
    exact CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three
      (K := K) (n := 4) (by norm_num) b c₀
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    haveI : Group.IsPerfect Q := ⟨hQ.1⟩
    exact s16lc_omegaMinus_center_three_free (F := K) (m := 4) (b := b) (d := c₀)
      (by norm_num) hirr (Q := Q) (e := eQ.trans hOm4)
  exact s168e3_three_not_dvd_centralizer_of_component_three_rank c hcomp hsimple hrank hcover

theorem s168e3_three_not_dvd_kBar_of_alt_nine_to_eleven
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn9 : 9 ≤ n) (hn11 : n ≤ 11)
    (hAlt : UC22.IsAlt ↥(lBar V₀ V hV L) n) :
    ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_alt (by omega) hAlt
  obtain ⟨eA⟩ := hAlt
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eA]
    exact CFSG.SectionRank.three_le_pRank_alternating (by omega)
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    haveI : Group.IsPerfect Q := ⟨hQ.1⟩
    have hZle : Nat.card (Subgroup.center Q) ≤ 2 :=
      CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt (n := n) (by omega) (eQ.trans eA)
    intro h3
    have hge : 3 ≤ Nat.card (Subgroup.center Q) := Nat.le_of_dvd Nat.card_pos h3
    omega
  exact s168e3_three_not_dvd_centralizer_of_component_three_rank c hcomp hsimple hrank hcover

theorem s168e3_three_not_dvd_kBar_of_omega_minus_six
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 6 1) :
    ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c1_isSimpleGroup_of_isOmegaMinus_six hOm
  obtain ⟨E, hE, hEcard⟩ := s15k_om6_exists_e27 hOm
  have hrank : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
    CFSG.SectionRank.le_pRank (p := 3) (k := 3) (by norm_num) (H := ⊤) (E := E)
      le_top hE (by rw [hEcard]; norm_num)
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hU4 : IsU4 (Q ⧸ Subgroup.center Q) 1 :=
      CFSG.Blueprint.LieModel.of_mulEquiv eQ.symm (isU4_of_isOmegaMinus_six hOm)
    have hdvd := rSchurOm6_holds Q hQ hU4
    intro h3
    have hge : 3 ≤ Nat.card (Subgroup.center Q) := Nat.le_of_dvd Nat.card_pos h3
    have hle2 : Nat.card (Subgroup.center Q) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  exact s168e3_three_not_dvd_centralizer_of_component_three_rank c hcomp hsimple hrank hcover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyEightLemmas
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFour
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem pRank_three_mulAut_bar_of_isL3 {L : Subgroup G} (hshape : IsL3 (Bar2 L) 2) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut (Bar2 L))) = 2 := by
  obtain ⟨K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hshape
  letI := hfield
  letI := hfin
  have hk : Nat.card K = 4 := by rw [hKcard]; norm_num
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (MulAut (Bar2 L))]
  exact CFSG.RankThree.PartTwo.KFacts.L34.pRank_three_mulAut_of_mulEquiv hk e

theorem seventeen_sixty (D : Data G) {V₀ V : Subgroup G}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h57 : R17_57At D V₀ V)
    (h1 : ∀ (hV : Hyp125 D V₀ V), R17_1At D V₀ V hV)
    (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h638 : UC6.R6_38 D) (h33 : R17_33_2At D V₀ V)
    (h22 : ∀ (hV : Hyp125 D V₀ V), R17_2_2At D V₀ V hV)
    (h23 : ∀ (hV : Hyp125 D V₀ V), R17_2_3At D V₀ V hV) : R17_60At D V₀ V := by
  intro L p ctx hLp
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hp : p.Prime := (D.sig_prime p hpmem).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpmem).2
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.memC
  have hsig1 : p ∈ D.sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns hpmem
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M := hSg.sig1_sp p hsig1
  have hM3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpmem
  have hLM : L ≤ D.M := ctx.memC.1.le
  have hNM : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp (ctx.hyp54.2 L ctx.memC).1
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range 2 p hp L D.M hNM
  have hker : CFSG.Open.pRank p
      ((CFSG.GroupTheory.conjModPCore 2 L D.M hNM).ker.map D.M.subtype) ≤
        CFSG.Open.pRank p (Sp D p) := by
    have hle : (CFSG.GroupTheory.conjModPCore 2 L D.M hNM).ker.map D.M.subtype ≤
        centSection D.M (Lp D p) (pCoreOf 2 (Lp D p)) := by
      rw [← hLp]
      intro m hm
      obtain ⟨hmM, hcomm⟩ := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L D.M hNM).mp hm
      exact ⟨hmM, hNM hmM, (hNM.trans (CFSG.Holt.General.NoRelevant.normalizer_le_normalizer_map
        (M := L) (K := CFSG.pCore 2 ↥L))) hmM, hcomm⟩
    calc CFSG.Open.pRank p ((CFSG.GroupTheory.conjModPCore 2 L D.M hNM).ker.map D.M.subtype)
        ≤ CFSG.Open.pRank p (centSection D.M (Lp D p) (pCoreOf 2 (Lp D p))) :=
          CFSG.SectionRank.pRank_mono hp.one_lt hle
      _ = CFSG.Open.pRank p (Sp D p) := (s13_pRank_pElementSubgroup hp _).symm
  have hp3 : p = 3 := by
    by_contra hp3
    have hrange : CFSG.Open.pRank p (CFSG.GroupTheory.conjModPCore 2 L D.M hNM).range ≤ 1 := by
      have htop : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1 := by
        refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hp ?_
        rw [card_mulAut_bar_of_isL3 ctx.shapeL]
        exact prime_sq_not_dvd_aut_L34 hp hp2 hp3
      exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans htop
    have hsmall : CFSG.Open.pRank p (Sp D p) ≤ 1 := h57 p ctx.hyp54
    omega
  subst hp3
  have hrange3 : CFSG.Open.pRank 3 (CFSG.GroupTheory.conjModPCore 2 L D.M hNM).range ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans
      (pRank_three_mulAut_bar_of_isL3 ctx.shapeL).le
  have hS3 : Sp D 3 ≠ ⊥ := by
    intro hbot
    have h0 : CFSG.Open.pRank 3 (Sp D 3) = 0 := by
      rw [hbot]
      exact CFSG.LocalAnalysis.GLTheoremB.MovingAround.Sec12b.pRank_bot (by norm_num)
    omega
  have hk1 : D.k = 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded D hsp
  have hbar : barImage D.M (Sp D 3) ≤ CFSG.pCore 3 (Bar2 D.M) :=
    barImage_Sp_le_pCore D ctx.hyp125 ctx.hyp54 hThin hCyc h638 h33
      (h22 ctx.hyp125) (h23 ctx.hyp125)
  have hpCoreM : IsPGroup 2 (CFSG.Open.pCoreOf 2 D.M) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hO2M : CFSG.Open.pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hbar_ne : barImage D.M (Sp D 3) ≠ ⊥ := by
    intro hbot
    have hle : Sp D 3 ≤ CFSG.Open.pCoreOf 2 D.M := by
      have hmap : ((Sp D 3).subgroupOf D.M).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) = ⊥ := hbot
      have hle' : (Sp D 3).subgroupOf D.M ≤
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker :=
        (Subgroup.map_eq_bot_iff (H := (Sp D 3).subgroupOf D.M)).mp hmap
      rw [QuotientGroup.ker_mk'] at hle'
      intro x hx
      have hxS : (⟨x, Sp_le D 3 hx⟩ : ↥D.M) ∈ (Sp D 3).subgroupOf D.M :=
        Subgroup.mem_subgroupOf.mpr hx
      have hker : (⟨x, Sp_le D 3 hx⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := hle' hxS
      exact Subgroup.mem_map_of_mem (Subgroup.subtype D.M) hker
    obtain ⟨s, hs, hsord⟩ :=
      s13_exists_orderOf_of_pElementSubgroup_ne_bot Nat.prime_three
        (H := centSection D.M (Lp D 3) (pCoreOf 2 (Lp D 3)))
        (by simpa [Sp, Opp] using hS3)
    have hsH : s ∈ CFSG.Open.pCoreOf 2 D.M := hle hs
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hpCoreM ⟨s, hsH⟩
    have h2 : orderOf s = 2 ^ m := (Subgroup.orderOf_coe _).trans hm
    rw [hsord] at h2
    have h3d : 3 ∣ 2 ^ m := by rw [← h2]
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3d
    have h23 : 3 = 2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp h32
    norm_num at h23
  have hP3ne : CFSG.pCore 3 (Bar2 D.M) ≠ ⊥ := by
    intro hbot
    exact hbar_ne (le_bot_iff.mp (hbar.trans (le_of_eq hbot)))
  set P3 : Subgroup (Bar2 D.M) := CFSG.pCore 3 (Bar2 D.M) with hP3def
  haveI hP3N : P3.Normal := by rw [hP3def]; exact CFSG.pCore_normal
  set Ω : Subgroup (Bar2 D.M) := CFSG.Walter.omegaOneCenter P3 3 with hΩdef
  have hΩle : Ω ≤ P3 := by rw [hΩdef]; exact CFSG.Walter.omegaOneCenter_le P3 3
  have hΩel : CFSG.Open.IsElemAbelian 3 Ω := by
    rw [hΩdef]
    refine ⟨IsMulCommutative.mk (Std.Commutative.mk ?_), ?_⟩
    · intro a b
      apply Subtype.ext
      exact ((Subgroup.mem_centralizer_iff.mp a.2.2.1) (b : Bar2 D.M) b.2.1).symm
    · intro x hx
      exact hx.2.2
  have hΩne : Ω ≠ ⊥ := by
    rw [hΩdef]
    exact CFSG.Walter.omegaOneCenter_ne_bot Nat.prime_three
      (CFSG.pCore_isPGroup (p := 3) (G := Bar2 D.M)) hP3ne
  have hΩN : Ω.Normal := by
    rw [hΩdef, ← Subgroup.normalizer_eq_top_iff]
    have hPtop : CFSG.GorensteinWalter.IsNormalIn P3 ⊤ :=
      ⟨le_top, fun h _ k hk => by simpa using hP3N.conj_mem k hk h⟩
    simpa using CFSG.Walter.le_normalizer_omegaOneCenter hPtop 3
  set N₁ : Subgroup G := barPreimage D.M Ω with hN₁def
  have hN₁M : N₁ ≤ D.M := s13_barPreimage_le D.M Ω
  have hN₁N : ∀ g ∈ D.M, ∀ x ∈ N₁, g * x * g⁻¹ ∈ N₁ :=
    s13_Bar13_barPreimage_conjInv hΩN
  have hmem : ∀ {Y : Subgroup (Bar2 D.M)} {x : G}, x ∈ barPreimage D.M Y ↔
      ∃ hx : x ∈ D.M,
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hx⟩ ∈ Y := by
    intro Y x
    rw [barPreimage, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      subst hyx
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hmk⟩
      exact ⟨⟨x, hx⟩, hmk, rfl⟩
  have hO2N₁ : CFSG.Open.pCoreOf 2 D.M ≤ N₁ := by
    intro x hx
    rw [hmem]
    have hxM : x ∈ D.M := hO2M hx
    refine ⟨hxM, ?_⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = (⟨x, hxM⟩ : ↥D.M) := Subtype.ext hyx
    rw [hyx'] at hy
    rw [show (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ = 1 from
      (QuotientGroup.eq_one_iff _).mpr hy]
    exact Ω.one_mem
  have hTN₁ : D.T ≤ Subgroup.normalizer (N₁ : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hN₁N t (D.sylowM.le ht) x hx
    · intro hx
      have h := hN₁N t⁻¹ (D.M.inv_mem (D.sylowM.le ht)) (t * x * t⁻¹) hx
      rwa [show t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x from by group] at h
  have hO2normM : D.M ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M)
  have hTO2 : D.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 D.M : Set G) :=
    D.sylowM.le.trans hO2normM
  have hN₁O2 : N₁ ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 D.M : Set G) :=
    hN₁M.trans hO2normM
  haveI hO2N : ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hO2N₁).mpr hN₁O2
  have hquot : ∀ a b : ↥N₁ ⧸ (CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) b
    have hxΩ : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(x : N₁).1, hN₁M x.2⟩ ∈ Ω :=
      (hmem.mp x.2).choose_spec
    have hyΩ : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(y : N₁).1, hN₁M y.2⟩ ∈ Ω :=
      (hmem.mp y.2).choose_spec
    have hcommΩ : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(x : N₁).1, hN₁M x.2⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(y : N₁).1, hN₁M y.2⟩ =
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(y : N₁).1, hN₁M y.2⟩ *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨(x : N₁).1, hN₁M x.2⟩ :=
      (by
        have h := hΩel.1.is_comm.comm ⟨_, hxΩ⟩ ⟨_, hyΩ⟩
        simpa using congrArg Subtype.val h)
    have hc : (x * y * x⁻¹ * y⁻¹ : ↥N₁) ∈
        (CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁ := by
      rw [Subgroup.mem_subgroupOf]
      have hM : ((x * y * x⁻¹ * y⁻¹ : ↥N₁) : G) ∈ D.M :=
        hN₁M (x * y * x⁻¹ * y⁻¹).2
      have himg : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
          ⟨((x * y * x⁻¹ * y⁻¹ : ↥N₁) : G), hM⟩ = 1 := by
        have heq : (⟨((x * y * x⁻¹ * y⁻¹ : ↥N₁) : G), hM⟩ : ↥D.M) =
            ⟨(x : N₁).1, hN₁M x.2⟩ * ⟨(y : N₁).1, hN₁M y.2⟩ *
              ⟨(x : N₁).1, hN₁M x.2⟩⁻¹ * ⟨(y : N₁).1, hN₁M y.2⟩⁻¹ :=
          Subtype.ext rfl
        rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hcommΩ]
        group
      have hker : (⟨((x * y * x⁻¹ * y⁻¹ : ↥N₁) : G), hM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := by
        rw [← QuotientGroup.eq_one_iff]; exact himg
      exact Subgroup.mem_map_of_mem D.M.subtype hker
    have h1 : QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁)
        (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    have h2 : QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁)
        (x * y * x⁻¹ * y⁻¹) =
        QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x *
          QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y *
          (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x)⁻¹ *
          (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [h2] at h1
    calc QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x *
          QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y
        = (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x *
            QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y *
            (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x)⁻¹ *
            (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y)⁻¹) *
          (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y *
            QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x) := by
          group
      _ = 1 * (QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y *
            QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x) := by rw [h1]
      _ = QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) y *
            QuotientGroup.mk' ((CFSG.Open.pCoreOf 2 D.M).subgroupOf N₁) x := one_mul _
  have h3Ω : 3 ∣ Nat.card Ω := by
    haveI : Nontrivial ↥Ω := (Subgroup.nontrivial_iff_ne_bot Ω).mpr hΩne
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥Ω)
    have hx3 : (x : ↥Ω) ^ 3 = 1 := Subtype.ext (hΩel.2 x x.2)
    have hord : orderOf x = 3 := by
      have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers x)
    rw [Nat.card_zpowers, hord] at h
    exact h
  have hdvdN₁ : Nat.card Ω ∣ Nat.card N₁ := by
    have h := Subgroup.card_map_dvd (N₁.subgroupOf D.M)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
    rw [show ((N₁.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))) = Ω by
      rw [hN₁def]
      exact s13_barImage_barPreimage D.M Ω] at h
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₁M).toEquiv] at h
  have h3N₁ : 3 ∣ Nat.card N₁ := h3Ω.trans hdvdN₁
  have hST : CFSG.Open.pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM)
  obtain ⟨E, hEN₁, hEel, hEcard, hEperm⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_permutes_of_abelian_quotient (B := N₁)
      (S := CFSG.Open.pCoreOf 2 D.M) (T := D.T) (r := 3) hquot hO2N₁ hST hTN₁ hTO2
      Nat.prime_three (by norm_num) hpCoreM
  have hEM : E ≤ D.M := hEN₁.trans hN₁M
  have hrankN₁ : 1 ≤ CFSG.Open.pRank 3 N₁ := by
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₁) 3 h3N₁
    have hx3 : (x : ↥N₁) ^ 3 = 1 := by
      rw [← hxord]; exact pow_orderOf_eq_one _
    have hzx : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (x : G)) := by
      rw [Subgroup.zpowers_eq_closure]
      refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
      · intro a ha b hb
        rw [Set.mem_singleton_iff] at ha hb
        rw [ha, hb]
      · intro a ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        simpa using congrArg Subtype.val hx3
    have hzxcard : Nat.card ↥(Subgroup.zpowers (x : G)) = 3 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
    have hmem₁ : 1 ∈ {k : ℕ | ∃ E : Subgroup G, E ≤ N₁ ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ k} :=
      ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2, hzx, by rw [hzxcard]; norm_num⟩
    exact le_csSup (CFSG.SectionRank.pRank_bddAbove (by norm_num) N₁) hmem₁
  have hrankE : 1 ≤ CFSG.Open.pRank 3 E := by
    have h1 : Nat.card ↥E = 3 ^ CFSG.Open.pRank 3 E :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hEel
    rw [h1] at hEcard
    have h2 : CFSG.Open.pRank 3 N₁ = CFSG.Open.pRank 3 E :=
      (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hEcard).symm
    omega
  obtain ⟨A₀, hA₀L, hA₀el, hA₀rank, hA₀perm⟩ :=
    exists_elemAbelian_permutes_of_isL3 (D := D) ctx.memC.1.le
      (ctx.hyp54.2 L ctx.memC).1 ctx.shapeL
  have hA₀M : A₀ ≤ D.M := hA₀L.trans hLM
  haveI hKstarSimple : IsSimpleGroup ↥(barImage D.M L) :=
    isSimple_barImage_of_shape ctx.memC hThin (Or.inr (Or.inr ctx.shapeL))
  haveI hKstarN : (barImage D.M L).Normal :=
    s13_barImage_normal (ctx.hyp54.2 L ctx.memC).1
  have hKinfP3 : (barImage D.M L) ⊓ P3 = ⊥ := by
    haveI hinfN : ((barImage D.M L) ⊓ P3).Normal :=
      Subgroup.normal_inf_normal (barImage D.M L) P3
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((barImage D.M L) ⊓ P3).subgroupOf (barImage D.M L)) with hbot | htop
    · rw [eq_bot_iff]
      intro x hx
      have hmem' : (⟨x, hx.1⟩ : ↥(barImage D.M L)) ∈
          ((barImage D.M L) ⊓ P3).subgroupOf (barImage D.M L) :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hbot] at hmem'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hmem'))
    · exfalso
      have hleK : barImage D.M L ≤ P3 := by
        intro x hx
        have hmem' : (⟨x, hx⟩ : ↥(barImage D.M L)) ∈
            ((barImage D.M L) ⊓ P3).subgroupOf (barImage D.M L) := by
          rw [htop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp hmem').2
      have hKsub : IsPGroup 3 ((barImage D.M L).subgroupOf P3) :=
        (CFSG.pCore_isPGroup (p := 3) (G := Bar2 D.M)).to_subgroup _
      have hK3 : IsPGroup 3 ↥(barImage D.M L) :=
        hKsub.of_equiv (Subgroup.subgroupOfEquivOfLe hleK)
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK3
      obtain ⟨e⟩ := s13_bar_equiv ctx.memC
      have hcard : Nat.card ↥(barImage D.M L) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by
        rw [show Nat.card ↥(barImage D.M L) = Nat.card (Bar2 L) from
          Nat.card_congr e.symm.toEquiv]
        exact card_bar_of_isL3 ctx.shapeL
      rw [hcard] at hk
      have hodd : Odd (3 ^ k) := (by norm_num : Odd (3 : ℕ)).pow
      rw [← hk] at hodd
      norm_num at hodd
  have hKP : ⁅barImage D.M L, P3⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_le_inf _ _).trans (le_of_eq hKinfP3))
  have hcommLN₁ : ⁅L, N₁⁆ ≤ CFSG.Open.pCoreOf 2 D.M := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haM : a ∈ D.M := hLM ha
    have hbM : b ∈ D.M := hN₁M hb
    have hbΩ : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨b, hbM⟩ ∈ Ω := (hmem.mp hb).choose_spec
    have hbP3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨b, hbM⟩ ∈ P3 := hΩle hbΩ
    have hM : (a * b * a⁻¹ * b⁻¹) ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (D.M.mul_mem haM hbM) (D.M.inv_mem haM)) (D.M.inv_mem hbM)
    have himg : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a * b * a⁻¹ * b⁻¹, hM⟩ = 1 := by
      have heq : (⟨a * b * a⁻¹ * b⁻¹, hM⟩ : ↥D.M) =
          ⟨a, haM⟩ * ⟨b, hbM⟩ * ⟨a, haM⟩⁻¹ * ⟨b, hbM⟩⁻¹ := Subtype.ext rfl
      rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hmem_comm : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a, haM⟩ *
          (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨b, hbM⟩ *
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨a, haM⟩)⁻¹ *
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨b, hbM⟩)⁻¹ ∈
          ⁅barImage D.M L, P3⁆ :=
        Subgroup.commutator_mem_commutator
          (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
            (Subgroup.mem_subgroupOf.mpr ha)) hbP3
      rw [hKP] at hmem_comm
      exact Subgroup.mem_bot.mp hmem_comm
    have hker : (⟨a * b * a⁻¹ * b⁻¹, hM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := by
      rw [← QuotientGroup.eq_one_iff]; exact himg
    exact Subgroup.mem_map_of_mem D.M.subtype hker
  have hdisj : A₀ ⊓ (E ⊔ CFSG.Open.pCoreOf 2 D.M) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨hxA₀, hxE⟩ := Subgroup.mem_inf.mp hx
    have hxN₁ : x ∈ N₁ := (sup_le hEN₁ hO2N₁) hxE
    have hxL : x ∈ L := hA₀L hxA₀
    have hxM : x ∈ D.M := hLM hxL
    have hxΩ : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈ Ω :=
      (hmem.mp hxN₁).choose_spec
    have hxP3 : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈ P3 := hΩle hxΩ
    have hxK : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈ barImage D.M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxL)
    have hxbot : (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ⟨x, hxM⟩ ∈
        (barImage D.M L) ⊓ P3 := ⟨hxK, hxP3⟩
    rw [hKinfP3, Subgroup.mem_bot] at hxbot
    have hxO : x ∈ CFSG.Open.pCoreOf 2 D.M := by
      have hker : (⟨x, hxM⟩ : ↥D.M) ∈ CFSG.pCore 2 ↥D.M := by
        rw [← QuotientGroup.eq_one_iff]; exact hxbot
      exact Subgroup.mem_map_of_mem D.M.subtype hker
    have hcop : Nat.Coprime (Nat.card A₀) (Nat.card (CFSG.Open.pCoreOf 2 D.M)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA₀el.isPGroup
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpCoreM
      rw [hk, hn]
      exact (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 2)).pow_right n
    have hdisjAO : A₀ ⊓ CFSG.Open.pCoreOf 2 D.M = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
    have hmem' : x ∈ A₀ ⊓ CFSG.Open.pCoreOf 2 D.M := ⟨hxA₀, hxO⟩
    rw [hdisjAO, Subgroup.mem_bot] at hmem'
    exact hmem'
  obtain ⟨n, hnO, hEel', hrank', hperm'⟩ :=
    exists_conj_sup_isElemAbelian_permutes (D := D) hA₀M hEM hA₀el hEel
      hA₀perm hEperm ((Subgroup.commutator_mono hA₀L hEN₁).trans hcommLN₁) hdisj (by omega)
  have hnM : n ∈ D.M := hO2M hnO
  have hE'M : A₀ ⊔ E.map (MulAut.conj n).toMonoidHom ≤ D.M := by
    refine sup_le hA₀M ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro e he
    exact D.M.mul_mem (D.M.mul_mem (by simpa using hnM) (hEM he)) (D.M.inv_mem hnM)
  exact false_of_permuting_elemAbelian_rank_two_of_k_one (D := D) (h1 ctx.hyp125) hk1
    hE'M hEel' hperm' hrank'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

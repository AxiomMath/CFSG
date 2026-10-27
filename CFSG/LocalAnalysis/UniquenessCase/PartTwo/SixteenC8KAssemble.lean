module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KP0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KHyp91
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KCaseTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KMinimal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KTranslate
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KThompson
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8TleBot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95Two
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SylowK
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KP0B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (I9 Hbar9)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

structure C8Glob (D : Data G) : Prop where
  hx : DataExt D
  hσ3 : SigmaThree D
  hSg : UC6S846.SigmaStd D
  h1219 : D.sig = D.sig1
  h61 : UC6.R6_1 D
  h1217 : R1217 D
  hSpA : RSp6SmallMod
  hSpC : RSp6SpinCent
  h95 : F09.R95Two D
  hu37 : U37Outer
  hSz : Inputs1719.K_CatalogueThreePrimeSz

structure C8KStageOne (D : Data G) (V₀ V L K : Subgroup G) (d : G) : Prop where
  dL : d ∈ L
  dK : d ∈ K
  dM : d ∈ D.M
  d3 : orderOf d = 3
  p0 : C8P0 (K ⊓ D.M) (K ⊓ F11.CTilde D.M V₀ V)
  c3 : ¬ 3 ∣ Nat.card ↥(K ⊓ F11.CTilde D.M V₀ V)
  rk : pRank 3 K ≤ 1
  ne_top : K ≠ ⊤
  hyp : F09.Hyp91 D (K ⊓ D.M) K (zpowers d)

theorem c8p0_normal {Γ : Type} [Group Γ] {B C : Subgroup Γ} (h : C8P0 B C) :
    (C.subgroupOf B).Normal := by
  unfold C8P0 at h
  obtain ⟨P, _, φ, -, hker, -, -⟩ := h
  rw [← hker]
  exact MonoidHom.normal_ker φ

theorem c8_stage_one (D : Data G) (hg : C8Glob D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {v₀ : IntMod V hV} {T₀ K T' : Subgroup G}
    (hs : C8KSetting D V₀ V L hV v₀ T₀ K T') : ∃ d : G, C8KStageOne D V₀ V L K d := by
  have hse := isStronglyPEmbedded_three D hg.hSg hg.h1219 hs.case8.2.2.1
  have hP := hs.sect.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hLM : L ≤ D.M := hs.sect.setting.hyp151.le
  obtain ⟨hperf, hLift, hIm⟩ := c8_lift_im D hg.h61 hg.h1217 hg.hSpA hg.hSpC hs
  obtain ⟨d, hd, hd3⟩ := c8_d_exists hLift hs.setUp.e64
  have hdK : d ∈ K := hs.setUp.mem.2.1 hd
  have hp0 := c8_p0 D hMs hIm hs.setUp.e64 hperf
  obtain ⟨hc3, hrk⟩ := c8k_c0_three D hg.h61 hse hs hp0 hd.1 hdK hd3
  have hKtop : K ≠ ⊤ := c8k_ne_top D.standing hs.setUp.mem.2.2.2
  exact ⟨d, hd.1, hdK, hLM hd.1, hd3, hp0, hc3, hrk, hKtop,
    c8_hyp91 D hse hKtop hs.setUp.mem.2.2.1 hdK (hLM hd.1) hd3 hrk⟩

theorem c8_stage_two (D : Data G) (hg : C8Glob D) {V₀ V L K : Subgroup G} {d : G}
    (hse : IsStronglyPEmbedded 3 D.M) (h1 : C8KStageOne D V₀ V L K d) :
    (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S K ∧ S ≤ D.M) ∧
      K = (K ⊓ D.M) ⊔ I9 K := by
  have hCY : K ⊓ F11.CTilde D.M V₀ V ≤ K ⊓ D.M :=
    inf_le_inf_left K (c8_cTilde_le D.M V₀ V)
  have hX := c8k_x_l3 hCY h1.c3 h1.p0
  obtain ⟨hS, hAlt⟩ := hg.h95 (K ⊓ D.M) K (zpowers d) h1.hyp h1.ne_top hX
  refine ⟨hS, ?_⟩
  rcases hAlt with ⟨e, -, -, hprod⟩ | ⟨e, he, hL, hS2⟩
  · exact hprod
  · exact (c8k_alt_two_false D hse hg.hu37 rfl h1.hyp hCY (c8p0_normal h1.p0) h1.c3 h1.p0
      h1.d3 he hL hS2).elim

theorem c8_kconf (D : Data G) (hg : C8Glob D) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {v₀ : IntMod V hV} {T₀ K T' : Subgroup G}
    (hs : C8KSetting D V₀ V L hV v₀ T₀ K T') :
    ∃ d : ↥K, C8KConf ↥K (c8kB D K) (c8kS K T') (c8kC0 D V₀ V K) d := by
  have hse := isStronglyPEmbedded_three D hg.hSg hg.h1219 hs.case8.2.2.1
  have hP := hs.sect.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hLM : L ≤ D.M := hs.sect.setting.hyp151.le
  obtain ⟨d, h1⟩ := c8_stage_one D hg hs
  obtain ⟨⟨S, hS, hSM⟩, hprod⟩ := c8_stage_two D hg hse h1
  have hCY : K ⊓ F11.CTilde D.M V₀ V ≤ K ⊓ D.M :=
    inf_le_inf_left K (c8_cTilde_le D.M V₀ V)
  have hK : CFSG.QuasithinUnique.CharTwo K := hs.setUp.mem.2.2.2
  have hd3 : orderOf (⟨d, h1.dK⟩ : ↥K) = 3 := (Subgroup.orderOf_mk d _).trans h1.d3
  refine ⟨⟨d, h1.dK⟩, ?_⟩
  exact
    { ctx :=
        { kgroup := uc22br4_isKGroup_catalog_of_open (D.standing.kProper.isKGroup K h1.ne_top)
          l3 := c8k_l3_of_prod inf_le_left hCY hprod h1.c3 h1.p0
          ne_top := fun h => hs.setUp.mem.2.2.1 (le_inf_iff.mp (Subgroup.subgroupOf_eq_top.mp h)).2
          prod := c8k_prod_of_alt hprod
          q_le := c8k_q_le_of_sylow hS hSM
          d_order := hd3
          d_cent := c8k_d_cent hse h1.dM hd3
          rank := c8k_rank D hg.hx hg.hσ3 hs.case8.2.2.1 hs.case8.2.2.2 hK }
      sylow := c8k_sylow_top hS hSM hs.setUp.sylowK
      s_le := c8k_s_le D hs.setUp.sylowM.le
      char2 := c8k_char2 hK
      c0_le := c8k_c0_le D V₀ V K
      p0 := c8p0_subgroupOf inf_le_left hCY h1.p0
      c0_cent := c8_c0_cent D hMs hLM hs.good h1.dL
      minimal := c8_minimal D hLM hs.good hs.setUp (c8k_q_le_of_sylow hS hSM) }

theorem c8InvThreePrimeGood_holds
    (D : Data G) (hg : C8Glob D) : C8InvThreePrimeGood D := by
  intro V₀ V L hV hS h8 hG v₀ T₀ K T' hU
  obtain ⟨d, conf⟩ := c8_kconf D hg (⟨hS, h8, hG, hU⟩ : C8KSetting D V₀ V L hV v₀ T₀ K T')
  exact c8_invthree_of_k (c8k_invol hg.hSz conf.ctx)

theorem c8TleKGood_holds
    (D : Data G) (hg : C8Glob D) : C8TleKGood D := by
  intro V₀ V L hV hS h8 hG v₀ T₀ K T' hU
  by_cases h0 : V₀ = ⊥
  · exact c8_tle_of_bot D hg.h1217 hg.hSpA hg.hSpC hS h8 h0 hU
  · obtain ⟨d, conf⟩ := c8_kconf D hg (⟨hS, h8, hG, hU⟩ : C8KSetting D V₀ V L hV v₀ T₀ K T')
    obtain ⟨ρ, O, Z, nat⟩ := c8k_natural_rep hg.hSz conf.ctx
    obtain ⟨w, hw, hw1, hw2, hwc, hwB⟩ := c8_exists_w D hS h0 hU
    obtain ⟨C, hC1, hCS, hCchar, hCn⟩ := c8k_exists_char_normal conf nat hw hw1 hw2 hwc hwB
    obtain ⟨C', hC'1, hC'S, hC'char, hC'n⟩ := c8_transport_char hC1 hCS hCchar hCn
    exact c8_le_of_charNormal D hU hC'1 hC'S hC'char hC'n

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

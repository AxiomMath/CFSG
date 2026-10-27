module

public import CFSG.Quasithin.MS93.Burnside.RigMain
public import CFSG.Quasithin.MS93.MRes45
public import CFSG.Quasithin.MS93.MS93FrontierDeep

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section Main

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] [Finite G]

theorem burnsideMS93R_s45data
    {M T L : Subgroup G} {F : Type} [Field F]
    [Fintype F] (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le))
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (h5 : Fintype.card F = 2 → MRes.S45C1BTwo) :
    (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2 ∧
      Nat.card ↥(Vq M L ⊓ Subgroup.centralizer (L : Set G)) = Fintype.card F ^ 2 ∧
      Vq M L ⊓ Subgroup.centralizer (L : Set G) ≤ Zq M L := by
  have h44 : S44 := s44_frontier s441_holds
    (S4A.s442_of_s441 ms14AS_holds sqtkQuot_holds s32_holds s43_holds s441_holds)
  have c : S45.Ctx M T L φ := S45.Ctx.ofItems s43_holds h44 h hmin hb hφ
  have hZV : c.HZV := by
    by_cases hq : Fintype.card F = 2
    · exact S45J.s45Q2a_holds G M T L F φ c hq
    · exact c.hZV_of_ne_two hq
  have hQ2b : c.HQ2b := by
    by_cases hq : Fintype.card F = 2
    · exact MRes.hQ2b_of_two ms14AS_holds sqtkQuot_holds (h5 hq) c hZV hq
    have hF4 := EmptyFaithful.Stellmacher.MS93Support.four_le_card_of_ne_two c hq
    intro p p' N hp hp' a ha h34 haN hpp' hU1 hU3
    have hQ4 := S45Q4.hQ4 c
    have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
    have hC1 : ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
        Hloc c.hyp.le L (p a) := by
      by_cases hZH : Zloc c.hyp.le L (p a) ≤ Hloc c.hyp.le L (p a)
      · exact inf_le_right.trans hZH
      · exact EmptyFaithful.Stellmacher.MS93Support.commutator_inf_zloc_le_hloc c hα
          (EmptyFaithful.Stellmacher.MS93Support.s45C1aQ4_holds G M T L F φ c hF4 (p a) hα)
          (EmptyFaithful.Stellmacher.MS93Support.burnsideRig_s45C1bQ4 ms14AS_holds sqtkQuot_holds
            G M T L F φ c hZV hF4 p N hp a ha h34 haN hZH)
    have hC4 := S45R.Ctx.not_frattiniIn_le c ms14AS_holds sqtkQuot_holds hZV hp ha h34 haN
    exact ⟨c.inf_centralizer_ltil_le ms14AS_holds sqtkQuot_holds hZV hQ4 hp hp' ha h34 haN hpp'
        hU1 hU3 hC1,
      c.center_le_uloc_sup_hloc ms14AS_holds sqtkQuot_holds hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
        hC1,
      c.frattiniIn_eq_vcirc ms14AS_holds sqtkQuot_holds hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3 hC1
        hC4,
      c.inf_centralizer_vcirc_le_whv ms14AS_holds sqtkQuot_holds hZV hQ4 hp hp' ha h34 haN hpp' hU1
        hU3,
      c.commutator_qv_ltil_le_top hZV hp hp' ha h34 haN hpp' hU3⟩
  obtain ⟨p, hp⟩ := c.exists_isGoodPath_of_ctx 28
  have hα := c.isMVtx_of_isGoodPath hp (k := 34) (by omega) (by decide)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hα (isMVtx_baseA _)
  obtain ⟨-, -, -, hHc, hF4, -, -, -, -, -⟩ :=
    c.exists_case13_of_isGoodPath ms14AS_holds sqtkQuot_holds hZV hQ2b
      (hp.smul g) (by omega) hg
  have hab := adj_baseA_baseB (puAmalgam h.le)
  have hA := isMVtx_baseA (puAmalgam h.le)
  have hT : (pCoreOf 2 M).relIndex T = Fintype.card F ^ 2 := by
    have := c.relIndex_qv hA hab
    rwa [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, puAmalgam.qv_baseB,
      S46.relIndex_imM h.le h.le] at this
  have hHZ : Hloc h.le L (baseA _) ≤ Zloc h.le L (baseA _) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hA)
  have hOM : pCoreOf 2 M ≤ M := pCoreOf_le' M
  have hZqM : Zq M L ≤ M := inf_le_left.trans (Xq_le M)
  have hCLM : Vq M L ⊓ Subgroup.centralizer (L : Set G) ≤ M := inf_le_left.trans (Vq_le h.L_le)
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hLt : Ltil h.le L (baseA _) = imM h.le L :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)
  have hZl : Zloc h.le L (baseA _) = imM h.le (Zq M L) :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer hZqM).2
      (le_normalizer_Zq h.le_normalizer))
  have hV : ⁅Qv (puAmalgam h.le) (baseA _), Ltil h.le L (baseA _)⁆ = imM h.le (Vq M L) := by
    rw [hQ, hLt, imM_commutator h.le hOM h.L_le]
  have eCL : imM h.le (Vq M L ⊓ Subgroup.centralizer (L : Set G)) = Hloc h.le L (baseA _) := by
    rw [imM_inf_centralizer h.le (Vq M L) h.L_le, ← hV, ← hLt, hF4]
  refine ⟨hT, ?_, ?_⟩
  · rw [← S45.card_imM h.le hCLM, eCL, hHc]
  · rw [← imM_le_imM_iff h.le hCLM, eCL, ← hZl]
    exact hHZ

end Main

end CFSG.Quasithin.MS93

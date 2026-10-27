module

public import CFSG.Quasithin.MS93.S4A43XJ

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace Ctx43

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {h : PUHyp M T L}
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx43 h φ)
include c

local notation "𝔛" => puAmalgam h.le
local notation "𝔘" => GoldAmalgam.Universal (puAmalgam h.le)
local notation "𝔄" => SimpleGraph.Adj (GoldAmalgam.treeGraph (puAmalgam h.le))

theorem mem_nablaSet_geo_four_six {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    geo 𝔛 α' α 6 ∈ nablaSet h.le L (geo 𝔛 α' α 4) := by
  have hb8 := c.eight_le_critDist
  have hθM := c.isMVtx_geo_rev hs (i := 6) (by omega) (by decide)
  have hd : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 6) (geo 𝔛 α' α 4) = 2 := by
    rw [tdist_comm, c.dist_rev_rev hs (by omega) (by omega)]
  exact (c.nabla_symm hθM hd).mp (c.mem_nablaSet_geo_six hs)

theorem lambda_facts {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') {g k : 𝔘}
    (hg : g ∈ stab 𝔛 (geo 𝔛 α' α 2)) (hg1 : g • geo 𝔛 α' α 1 = geo 𝔛 α' α 3)
    (hk : k ∈ stab 𝔛 (geo 𝔛 α' α 4)) (hk3 : k • geo 𝔛 α' α 3 = geo 𝔛 α' α 5) :
    𝔄 (geo 𝔛 α' α 5) (k • g • α') ∧ IsMVtx 𝔛 (k • g • α') ∧
      Uloc h.le L (k • g • α') ⊓ ZM 𝔛 (geo 𝔛 α' α 6) ≤ stabCenter 𝔛 (geo 𝔛 α' α 6) ∧
      k • g • α' ≠ geo 𝔛 α' α 6 ∧ k • g • α' ∉ nablaSet h.le L (geo 𝔛 α' α 6) := by
  have hb8 := c.eight_le_critDist
  obtain ⟨hμ3, hμM, -, -⟩ := c.mu_facts hs hg hg1
  obtain ⟨-, -, hUlam⟩ := c.vi_four_le_centralizer_lambda hs hg hg1 hk hk3
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hθM := c.isMVtx_geo_rev hs (i := 6) (by omega) (by decide)
  have hζH := c.not_isMVtx_geo_rev hs (i := 5) (by omega) (by decide)
  have hη5 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := c.adj_geo_rev hs (i := 4) (by omega)
  have h56 : 𝔄 (geo 𝔛 α' α 5) (geo 𝔛 α' α 6) := c.adj_geo_rev hs (i := 5) (by omega)
  have hlam : 𝔄 (geo 𝔛 α' α 5) (k • g • α') := by
    have := (adj_smul _ k _ _).mpr hμ3
    rwa [hk3] at this
  have hlamM : IsMVtx 𝔛 (k • g • α') := (isMVtx_smul _ k _).mpr hμM
  have hkη : k • geo 𝔛 α' α 4 = geo 𝔛 α' α 4 := (mem_stab _).mp hk
  have hUZ : Uloc h.le L (k • g • α') ⊓ ZM 𝔛 (geo 𝔛 α' α 6) ≤ stabCenter 𝔛 (geo 𝔛 α' α 6) := by
    by_contra hn
    have hZeq := c.concl434 _ _ _ hζH hlam h56 hn
    apply c.not_mem_nablaSet_mu hs hg hg1
    have hdη : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) (k • g • α') = 2 := by
      rw [← hkη, dist_smul, c.dist_four_mu hs hg hg1]
    have hlamη : k • g • α' ∈ nablaSet h.le L (geo 𝔛 α' α 4) := by
      refine ⟨hdη, ?_⟩
      rw [zv_of_isMVtx _ hlamM, hZeq, ← zv_of_isMVtx _ hθM]
      exact (c.mem_nablaSet_geo_four_six hs).2
    rw [← hkη] at hlamη
    exact (mem_nablaSet_smul h k _ _).mp hlamη
  have hne : k • g • α' ≠ geo 𝔛 α' α 6 := by
    intro he
    rw [he, inf_eq_left.mpr (uloc_le_zm h c.full hθM)] at hUZ
    have hbot : Uloc h.le L (geo 𝔛 α' α 6) = ⊥ := by
      rw [eq_bot_iff, ← c.uloc_inf_stabCenter hθM]
      exact le_inf le_rfl hUZ
    have hcard := c.card_uloc hθM
    rw [hbot, Subgroup.card_bot] at hcard
    have : 1 < Fintype.card F := Fintype.one_lt_card
    have h8 : 2 ^ 3 ≤ Fintype.card F ^ 3 := Nat.pow_le_pow_left (by omega) 3
    omega
  refine ⟨hlam, hlamM, hUZ, hne, fun hmem => ?_⟩
  have hZeq : ZM 𝔛 (k • g • α') = ZM 𝔛 (geo 𝔛 α' α 4) :=
    c.zm_eq_of_mem_nablaSet hθM h56.symm hlam hη5.symm hmem (c.mem_nablaSet_geo_six hs)
  have hle : critR0 𝔛 α α' ≤ Uloc h.le L (geo 𝔛 α' α 4) ⊓ stabCenter 𝔛 (geo 𝔛 α' α 4) := by
    refine le_inf ?_ (c.critR0_le_stabCenter_four hs)
    rw [hUlam, Usup, zv_of_isMVtx _ hlamM, hZeq, ← zv_of_isMVtx _ hηM, ← Usup]
    exact c.usup_le_uloc hηM hη5
  rw [c.uloc_inf_stabCenter hηM, le_bot_iff] at hle
  have hcard := c.card_critR0 hs
  rw [hle, Subgroup.card_bot] at hcard
  have : 1 < Fintype.card F := Fintype.one_lt_card
  nlinarith

theorem critR0_le_stabCenter_six {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') :
    critR0 𝔛 α α' ≤ stabCenter 𝔛 (geo 𝔛 α' α 6) := by
  have hb8 := c.eight_le_critDist
  have hγ1 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) := (c.adj_geo_rev hs (i := 1) (by omega)).symm
  have hγ3 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := c.adj_geo_rev hs (i := 2) (by omega)
  have hη3 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 3) := (c.adj_geo_rev hs (i := 3) (by omega)).symm
  have hη5 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := c.adj_geo_rev hs (i := 4) (by omega)
  have h56 : 𝔄 (geo 𝔛 α' α 5) (geo 𝔛 α' α 6) := c.adj_geo_rev hs (i := 5) (by omega)
  obtain ⟨g, hg, hg1⟩ := exists_mem_stab_smul _ hγ1 hγ3
  obtain ⟨k, hk, hk3⟩ := exists_mem_stab_smul _ hη3 hη5
  obtain ⟨-, -, hUlam⟩ := c.vi_four_le_centralizer_lambda hs hg hg1 hk hk3
  obtain ⟨hlam, hlamM, hUZ, -, -⟩ := c.lambda_facts hs hg hg1 hk hk3
  refine le_trans ?_ hUZ
  rw [hUlam]
  exact le_inf (c.usup_le_uloc hlamM hlam.symm)
    ((c.usup_le_zh hlamM hlam.symm).trans (zh_le_zm _ h56.symm))

theorem vi_six_le_qv {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : Vi 𝔛 α 6 ≤ Qv 𝔛 (geo 𝔛 α' α 6) := by
  have hb8 := c.eight_le_critDist
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hd6 := c.dist_geo_rev hs (i := 6) (by omega)
  obtain ⟨z, hcz, hdz, hdη⟩ := c.exists_crit_four hs
  have hcz' : IsCritical 𝔛 (geo 𝔛 α' α 4) z := ms22_iii _ h.hyp20 h.critDist_pos c.cent hcz
  have hsz : Star 𝔛 z (geo 𝔛 α' α 4) := c.star_of_crit hcz'
  have hnot := c.not_mem_nablaSet_geo_four hsz
  have hdηz : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) z = critDist 𝔛 := hcz'.2.1
  have hsum : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) α +
      (puAmalgam h.le).treeGraph.dist α z = (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) z := by
    rw [tdist_comm _ (geo 𝔛 α' α 4) α, hdη, tdist_comm _ α z, hdz, hdηz]
    omega
  have hg2 : geo 𝔛 (geo 𝔛 α' α 4) z 2 = geo 𝔛 α' α 6 := by
    rw [geo_eq_geo_of_dist_add _ hsum (by rw [tdist_comm, hdη]; omega),
      geo_tail _ (by rw [hd']; omega)]
  have hg4 : geo 𝔛 (geo 𝔛 α' α 4) z 4 = geo 𝔛 α' α 8 := by
    rw [geo_eq_geo_of_dist_add _ hsum (by rw [tdist_comm, hdη]; omega),
      geo_tail _ (by rw [hd']; omega)]
  rw [hg2, hg4] at hnot
  refine vi_le_of_forall_zm _ hs.1.1 fun t ht hdt => ?_
  rcases le_qv_or_crit _ ht (w := geo 𝔛 α' α 6) (a := α) (k := 6) (by omega)
      (by rw [tdist_comm]; exact hdt) (by rw [hd6]) with hQ | ⟨hcrit, hta, -⟩
  · exact hQ
  · exfalso
    apply hnot
    have hmem := c.mem_nablaSet_geo_two' hcrit
    have hdθt : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 6) t = critDist 𝔛 := by
      rw [tdist_comm]; exact hcrit.2.1
    have hsum' : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 6) α +
        (puAmalgam h.le).treeGraph.dist α t =
          (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 6) t := by
      rw [tdist_comm _ (geo 𝔛 α' α 6) α, hd6, tdist_comm _ α t, hta, hdθt]
      omega
    rw [geo_eq_geo_of_dist_add _ hsum' (by rw [tdist_comm, hd6]; omega),
      geo_tail _ (by rw [hd']; omega)] at hmem
    exact hmem

theorem false_of_star {α α' : Vtx 𝔛} (hs : Star 𝔛 α α') : False := by
  have hb8 := c.eight_le_critDist
  have hα := hs.1.1
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist 𝔛 := (c.crit_symm hs).2.1
  have hαβ : 𝔄 α (geo 𝔛 α α' 1) := adj_geo_one_of_isCritical _ h.critDist_pos hs.1
  have hγM := c.isMVtx_geo_two' hs
  have hηM := c.isMVtx_geo_rev hs (i := 4) (by omega) (by decide)
  have hθM := c.isMVtx_geo_rev hs (i := 6) (by omega) (by decide)
  have hγ1 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 1) := (c.adj_geo_rev hs (i := 1) (by omega)).symm
  have hγ3 : 𝔄 (geo 𝔛 α' α 2) (geo 𝔛 α' α 3) := c.adj_geo_rev hs (i := 2) (by omega)
  have hη3 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 3) := (c.adj_geo_rev hs (i := 3) (by omega)).symm
  have hη5 : 𝔄 (geo 𝔛 α' α 4) (geo 𝔛 α' α 5) := c.adj_geo_rev hs (i := 4) (by omega)
  have hθ5 : 𝔄 (geo 𝔛 α' α 6) (geo 𝔛 α' α 5) := (c.adj_geo_rev hs (i := 5) (by omega)).symm
  have hθ7 : 𝔄 (geo 𝔛 α' α 6) (geo 𝔛 α' α 7) := c.adj_geo_rev hs (i := 6) (by omega)
  obtain ⟨g, hg, hg1⟩ := exists_mem_stab_smul _ hγ1 hγ3
  obtain ⟨k, hk, hk3⟩ := exists_mem_stab_smul _ hη3 hη5
  obtain ⟨k', hk', hk5⟩ := exists_mem_stab_smul _ hθ5 hθ7
  obtain ⟨hμ3, hμM, -, hγμ⟩ := c.mu_facts hs hg hg1
  obtain ⟨-, hZμ, hUlam⟩ := c.vi_four_le_centralizer_lambda hs hg hg1 hk hk3
  obtain ⟨hlam, hlamM, -, hne, hnot⟩ := c.lambda_facts hs hg hg1 hk hk3
  have hUρ : critR0 𝔛 α α' = Usup 𝔛 (k' • k • g • α') (geo 𝔛 α' α 7) := by
    rw [← hk5]
    exact eq_usup_smul _ (c.critR0_le_stabCenter_six hs) hUlam hk'
  have hρ7 : 𝔄 (geo 𝔛 α' α 7) (k' • k • g • α') := by
    have := (adj_smul _ k' _ _).mpr hlam
    rwa [hk5] at this
  have hρM : IsMVtx 𝔛 (k' • k • g • α') := (isMVtx_smul _ k' _).mpr hlamM
  have hdθ : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 6) (k • g • α') = 2 :=
    dist_eq_two_of_adj_adj _ hθ5 hlam hne.symm
  have hZlam : ZM 𝔛 (k • g • α') ≤ ZM 𝔛 (k' • k • g • α') ⊔ ZM 𝔛 (geo 𝔛 α' α 6) :=
    c.zm_le_zm_smul_sup_of_not_mem hθM hdθ hnot hk'
  have hcρ : Vi 𝔛 α 6 ≤ Subgroup.centralizer (ZM 𝔛 (k' • k • g • α') : Set 𝔘) :=
    vi_le_of_forall_zm _ hα fun t ht hdt =>
      c.commute_zm_of_shift (k := 3) (by omega)
        (fun x x' hsx => c.critR0_le_stabCenter_six hsx) hs hρM hρ7 hUρ ht hdt
  have hV6 := c.vi_six_le_qv hs
  have hclam : Vi 𝔛 α 6 ≤ Subgroup.centralizer (ZM 𝔛 (k • g • α') : Set 𝔘) := by
    rw [Subgroup.le_centralizer_iff]
    refine hZlam.trans (sup_le (Subgroup.le_centralizer_iff.mp hcρ) ?_)
    exact (zm_le_centralizer_qv _ h.hyp20 hθM).trans (Subgroup.centralizer_le hV6)
  have hcμ : Vi 𝔛 α 6 ⊓ Qv 𝔛 (geo 𝔛 α' α 4) ≤
      Subgroup.centralizer (ZM 𝔛 (g • α') : Set 𝔘) := by
    rw [Subgroup.le_centralizer_iff]
    refine hZμ.trans (sup_le ?_ ?_)
    · exact (Subgroup.le_centralizer_iff.mp hclam).trans (Subgroup.centralizer_le inf_le_left)
    · exact (zm_le_centralizer_qv _ h.hyp20 hηM).trans (Subgroup.centralizer_le inf_le_right)
  have hYμ : Vi 𝔛 α 6 ⊓ Qv 𝔛 (geo 𝔛 α' α 4) ≤ Qv 𝔛 (g • α') := by
    rw [← c.cent (g • α') _ hμM hμ3.symm]
    exact le_inf (inf_le_right.trans (qv_le_qv _ h.hyp20 hηM hη3)) hcμ
  have hHμ := (c.concl432 hμM).2 _ hγμ
  have hdμγ : (puAmalgam h.le).treeGraph.dist (g • α') (geo 𝔛 α' α 2) = 2 := hγμ.1
  have hadj : 𝔄 (geo 𝔛 (g • α') (geo 𝔛 α' α 2) 1) (geo 𝔛 α' α 2) := by
    have := adj_geo (puAmalgam h.le) (u := g • α') (w := geo 𝔛 α' α 2) (i := 1) (by omega)
    rwa [show geo 𝔛 (g • α') (geo 𝔛 α' α 2) (1 + 1) = geo 𝔛 α' α 2 from
      geo_of_le _ (by omega)] at this
  have hfinH : Finite ↥(Hloc h.le L (g • α')) := by
    rw [hHμ.1, hHμ.2]
    have := finite_qv _ h.hyp20 (by rw [← isMVtx_iff_of_adj _ hadj.symm]; exact hγM)
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((c.usup_le_zh hγM hadj.symm).trans (zh_le_qv _ _)))
  have hcardH : Nat.card ↥(Hloc h.le L (g • α')) = Fintype.card F ^ 2 := by
    rw [hHμ.1, hHμ.2, c.card_usup hγM hadj.symm]
  have hVcμV : Vcirc h.le L (g • α') ≤ Vv 𝔛 (g • α') :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h _).trans (stab_le_normalizer_vv h _))
  have hVcβ : Vcirc h.le L (g • α') ≤ Qv 𝔛 (geo 𝔛 α α' 1) := by
    refine hVcμV.trans (vv_le_qv_of_dist h hμM ?_)
    have := dist_triangle (puAmalgam h.le) (g • α') (geo 𝔛 α' α 3) (geo 𝔛 α α' 1)
    rw [dist_eq_one_of_adj _ hμ3.symm, c.dist_rev_geo_one hs (by omega)] at this
    omega
  have hXα := c.not_vcirc_le_qv hs hg
  have hd4 := c.dist_geo_rev hs (i := 4) (by omega)
  have hVY : Vv 𝔛 α ≤ Vi 𝔛 α 6 ⊓ Qv 𝔛 (geo 𝔛 α' α 4) :=
    le_inf (vi_le_vi_of_dist _ (by simp)) (vv_le_qv_of_dist h hα (by rw [hd4]; omega))
  have hYH : ⁅Vi 𝔛 α 6 ⊓ Qv 𝔛 (geo 𝔛 α' α 4), Vcirc h.le L (g • α')⁆ ≤
      Hloc h.le L (g • α') := by
    rw [Hloc, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hYμ
  have hsq := sq_le_card_commutator_vv h c.full c.cent c.hb hα hαβ c.via (c.isC1 hα) hVcβ hXα
  have hEq : ⁅Vv 𝔛 α, Vcirc h.le L (g • α')⁆ = Hloc h.le L (g • α') := by
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.commutator_mono hVY le_rfl).trans hYH) ?_
    rw [hcardH]
    exact hsq
  have hYV : ⁅Vi 𝔛 α 6 ⊓ Qv 𝔛 (geo 𝔛 α' α 4), Vcirc h.le L (g • α')⁆ ≤ Vv 𝔛 α := by
    refine hYH.trans (hEq.symm ▸ ?_)
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hVcβ.trans (qv_le_stab_of_adj _ hαβ.symm)).trans (stab_le_normalizer_vv h α))
  obtain ⟨z, hcz, hdz, hdη⟩ := c.exists_crit_four hs
  have hsz : Star 𝔛 (geo 𝔛 α' α 4) z := c.star_of_crit hcz
  have hc := c.concl438_c hsz
  have hdzη : (puAmalgam h.le).treeGraph.dist z (geo 𝔛 α' α 4) = critDist 𝔛 := hcz.2.1
  have hz4 : geo 𝔛 z (geo 𝔛 α' α 4) 4 = α :=
    (eq_geo_of_dist _ hdz (by rw [hdz, hdη, hdzη]; omega)).symm
  have hsum : (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) α +
      (puAmalgam h.le).treeGraph.dist α z = (puAmalgam h.le).treeGraph.dist (geo 𝔛 α' α 4) z := by
    rw [tdist_comm _ (geo 𝔛 α' α 4) α, hdη, tdist_comm _ α z, hdz, tdist_comm, hdzη]
    omega
  have hη1 : geo 𝔛 (geo 𝔛 α' α 4) z 1 = geo 𝔛 α' α 5 := by
    rw [geo_eq_geo_of_dist_add _ hsum (by rw [tdist_comm, hdη]; omega),
      geo_tail _ (by rw [hd']; omega)]
  rw [hz4, hη1] at hc
  have hV4θ : Vi 𝔛 α 4 ≤ Qv 𝔛 (geo 𝔛 α' α 6) :=
    vi_le_qv' _ (by rw [c.dist_geo_rev hs (by omega)]; omega)
  have hθ5le : Qv 𝔛 (geo 𝔛 α' α 6) ≤ Qv 𝔛 (geo 𝔛 α' α 5) := qv_le_qv _ h.hyp20 hθM hθ5
  have hV4n : Vi 𝔛 α 4 ≤ Subgroup.normalizer (Qv 𝔛 (geo 𝔛 α' α 4) : Set 𝔘) :=
    (hV4θ.trans hθ5le).trans ((qv_le_stab_of_adj _ hη5.symm).trans (stab_le_normalizer_qv _ _))
  have hV46 : Vi 𝔛 α 4 ≤ Vi 𝔛 α 6 := vi_le_vi_of_dist _ (by simp)
  have hdec : Vi 𝔛 α 6 ≤ Vi 𝔛 α 4 ⊔ (Vi 𝔛 α 6 ⊓ Qv 𝔛 (geo 𝔛 α' α 4)) := by
    intro x hx
    have hx' : x ∈ ((Vi 𝔛 α 4 ⊔ Qv 𝔛 (geo 𝔛 α' α 4) : Subgroup 𝔘) : Set 𝔘) := by
      rw [hc]
      exact hθ5le (hV6 hx)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hV4n] at hx'
    obtain ⟨a, ha, q, hq, rfl⟩ := hx'
    have hqV : q ∈ Vi 𝔛 α 6 := by
      have : q = a⁻¹ * (a * q) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hV46 ha)) hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hqV, hq⟩)
  have hVcn4 : Vcirc h.le L (g • α') ≤ Subgroup.normalizer (Vi 𝔛 α 4 : Set 𝔘) :=
    (hVcβ.trans (qv_le_stab_of_adj _ hαβ.symm)).trans (stab_le_normalizer_vi' _ α 4)
  have hV6α : Vi 𝔛 α 6 ≤ stab 𝔛 α := (vi_le_qv' _ (by simp; omega)).trans (qv_le_stab _ α)
  have hXW : ⁅Vi 𝔛 α 6, Vcirc h.le L (g • α')⁆ ≤ Vi 𝔛 α 4 := by
    refine (Subgroup.commutator_mono hdec le_rfl).trans ?_
    refine S4A.commutator_sup_le_of ?_ ?_ Subgroup.le_normalizer
      ((inf_le_left.trans hV6α).trans (stab_le_normalizer_vi' _ α 4))
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp hVcn4
    · exact hYV.trans (vi_le_vi_of_dist _ (by simp))
  have hker := commutator_ltil_le_of_comm_le h c.full hα hαβ (stab_le_normalizer_vi' _ α 6)
    hVcβ hXα (stab_le_normalizer_vi' _ α 4) hXW
  exact c.false_of_commutator_vi_ltil_le hα hαβ (i := 5) (by omega) (by omega) hker

end Ctx43

theorem s43b6_of (h32 : S32) (h431A : S431A) (h431B : S431B) (h432 : S432) : S43b6 := by
  intro G _ _ M T L h F _ _ φ hH _ α α' hs
  exact (ctx43_of h φ h32 h431A h431B h432 hH hs).false_of_star hs

end CFSG.Quasithin.MS93.S4A

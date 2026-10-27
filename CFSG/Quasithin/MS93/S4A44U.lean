module

public import CFSG.Quasithin.MS93.S4A44Base
public import CFSG.Quasithin.MS93.S4A431F
public import CFSG.Quasithin.MS93.S46Type
public import CFSG.Quasithin.MS93.S46Gen
public import CFSG.Quasithin.MS93.S38Base

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Card

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem le_card_commutator_uloc {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) {P : Subgroup (puAmalgam h.le).Universal}
    (hP : P ≤ Qv (puAmalgam h.le) ρ) (hne : ⁅Uloc h.le L δ, P⁆ ≠ ⊥) :
    Fintype.card F ≤ Nat.card ↥⁅Uloc h.le L δ, P⁆ := by
  obtain ⟨d, -, hcard⟩ := S46.card_commutator_uloc_le h hφ hδ hδρ hP
  rcases d with _ | d
  · exact absurd (Subgroup.card_eq_one.mp (by rw [hcard, pow_zero])) hne
  · rw [hcard]
    exact Nat.le_self_pow (by omega) _

theorem usup_ne_bot (hC : CentHyp (puAmalgam h.le)) {α β : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Usup (puAmalgam h.le) α β ≠ ⊥ := by
  intro hbot
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  rw [Usup, zv_of_isMVtx _ hα, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  have hle : Qv (puAmalgam h.le) β ≤ Qv _ α := by
    rw [← hC α β hα hαβ]
    exact le_inf le_rfl (Subgroup.le_centralizer_iff.mp hbot)
  have heq : Qv (puAmalgam h.le) β = Qv _ α :=
    le_antisymm hle (qv_le_qv _ h.hyp20 hα hαβ)
  apply not_stab_le_normalizer_qv _ h.hyp20 hα hαβ
  rw [heq]
  exact stab_le_normalizer_qv _ α

omit [Fintype F] hφ in
theorem card_usup_eq_of_edge {α β δ ρ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) (hδ : IsMVtx _ δ)
    (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ) :
    Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Nat.card ↥(Usup (puAmalgam h.le) α β) := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_of_isMVtx _ hα hαβ hδ hδρ
  rw [usup_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem critR_eq_usup_of_card (hC : CentHyp (puAmalgam h.le)) {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hq : Nat.card ↥(Usup (puAmalgam h.le) α' (geo _ α' α 1)) = Fintype.card F) :
    ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ = Usup (puAmalgam h.le) α' (geo _ α' α 1) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb0 hC hc
  have hα' := hc.isMVtx_right _ h.hyp20
  have hadj := adj_geo_one_of_isCritical _ hb0 hc'
  have hZ : ZM (puAmalgam h.le) α ≤ Qv _ (geo _ α' α 1) := zm_le_qv_geo_one_left _ h.hyp20 hb0 hC hc
  have hZs : ZM (puAmalgam h.le) α ≤ stab _ α' := hZ.trans (qv_le_stab_of_adj _ hadj.symm)
  have hR : ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ = ⁅Uloc h.le L α', ZM _ α⁆ := by
    rw [Subgroup.commutator_comm, commutator_zm_eq_uloc h hfull hα' hZs]
  have hle : ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ ≤ Usup (puAmalgam h.le) α' (geo _ α' α 1) := by
    rw [Usup, zv_of_isMVtx _ hα', Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hZ
  have hne : ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ≠ ⊥ := by
    rw [← hR]
    exact ms22_ii _ h.hyp20 hb0 hC hc
  have hcard := le_card_commutator_uloc h hφ hα' hadj hZ hne
  rw [← hR] at hcard
  have : Finite ↥(Usup (puAmalgam h.le) α' (geo _ α' α 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hq]; exact Fintype.card_ne_zero)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hq]; exact hcard)

theorem not_stab_le_normalizer_of_le_uloc {α : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α)
    {N : Subgroup (puAmalgam h.le).Universal} (hNU : N ≤ Uloc h.le L α) (hN : N ≠ ⊥)
    (hNc : Nat.card ↥N < Fintype.card F ^ 3) :
    ¬ stab (puAmalgam h.le) α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) := by
  intro hn
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hα
  obtain ⟨n, hnN, hn1⟩ := (Subgroup.bot_or_exists_ne_one N).resolve_left hN
  have hcU : Nat.card ↥(Uloc h.le L α) = Fintype.card F ^ 3 := by
    rw [card_eq_of_natural hψ, Nat.card_eq_fintype_card]
  have hUN : Uloc h.le L α ≤ N := by
    intro u hu
    set e := natCoord hψ
    have hn0 : Multiplicative.toAdd (e ⟨n, hNU hnN⟩) ≠ 0 := by
      intro h0
      have h1 : e ⟨n, hNU hnN⟩ = 1 := h0
      rw [MulEquiv.map_eq_one_iff] at h1
      exact hn1 (congrArg Subtype.val h1)
    by_cases hu0 : Multiplicative.toAdd (e ⟨u, hu⟩) = 0
    · have h1 : e ⟨u, hu⟩ = 1 := hu0
      rw [MulEquiv.map_eq_one_iff] at h1
      rw [show u = 1 from congrArg Subtype.val h1]
      exact N.one_mem
    obtain ⟨g₁, hg₁⟩ := exists_mulVec_e0_eq hn0
    obtain ⟨g₂, hg₂⟩ := exists_mulVec_e0_eq hu0
    obtain ⟨a, ha⟩ := toSL3_surjective hψs (g₂ * g₁⁻¹)
    have hconj : (a : (puAmalgam h.le).Universal) * n * (a : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L α :=
      (stab_le_normalizer_uloc h α a.2 n).mp (hNU hnN)
    have hcoord := natCoord_conj hψ a ⟨n, hNU hnN⟩ ⟨_, hconj⟩ rfl
    have hval : (⟨_, hconj⟩ : ↥(Uloc h.le L α)) = ⟨u, hu⟩ := by
      apply e.injective
      apply Multiplicative.toAdd.injective
      rw [hcoord]
      have hφa : ((ψ a : Matrix.GeneralLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
          ((toSL3 ψ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) := (coe_toSL3 ψ a).symm
      rw [hφa, ha, ← hg₁, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
        inv_mul_cancel_right, hg₂]
    have : u = (a : (puAmalgam h.le).Universal) * n * (a : (puAmalgam h.le).Universal)⁻¹ :=
      (congrArg Subtype.val hval).symm
    rw [this]
    exact (hn a.2 n).mp hnN
  have : Finite ↥(Uloc h.le L α) := Nat.finite_of_card_ne_zero (by
    rw [hcU]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have : Finite ↥N := Finite.of_injective _ (Subgroup.inclusion_injective hNU)
  have := Subgroup.card_le_of_le hUN
  omega

omit [Fintype F] hφ in
theorem qv_le_normalizer_usup {α β : Vtx (puAmalgam h.le)}
    (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Qv (puAmalgam h.le) β ≤
      Subgroup.normalizer (Usup (puAmalgam h.le) α β : Set (puAmalgam h.le).Universal) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  have hgα : g • α = α := (mem_stab _).mp (qv_le_stab_of_adj _ hαβ.symm hg)
  have hgβ : g • β = β := (mem_stab _).mp (qv_le_stab _ β hg)
  rw [← usup_smul, hgα, hgβ]

theorem card_usup_eq_sq (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    {α β : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hαβ : (puAmalgam h.le).treeGraph.Adj α β) :
    Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2 := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hcases : Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ∨
      Nat.card ↥(Usup (puAmalgam h.le) α β) = Fintype.card F ^ 2 := by
    have hne := usup_ne_bot h hφ hC hα hαβ
    rw [usup_eq_commutator_uloc h hfull hα hαβ] at hne ⊢
    obtain ⟨d, hd, hcard⟩ := S46.card_commutator_uloc_le h hφ hα hαβ le_rfl
    interval_cases d
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hcard, pow_zero])) hne
    · left
      rw [hcard, pow_one]
    · right
      exact hcard
  refine hcases.resolve_left fun hq => ?_
  have hq' : ∀ δ ρ : Vtx (puAmalgam h.le), IsMVtx _ δ → (puAmalgam h.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam h.le) δ ρ) = Fintype.card F := fun δ ρ hδ hδρ =>
    (card_usup_eq_of_edge h hα hαβ hδ hδρ).trans hq
  have hXM : ∀ δ : Vtx (puAmalgam h.le), IsMVtx _ δ → XM _ δ = ZM _ δ :=
    fun δ hδ => xm_eq_zm h hfull hδ
  have hfinU : Finite ↥(Usup (puAmalgam h.le) α β) :=
    Nat.finite_of_card_ne_zero (by rw [hq]; exact Fintype.card_ne_zero)
  have key := ms23 _ h.hyp20 hα hαβ (by omega) (h.gen23At hα hαβ)
    (Aαβ := Usup (puAmalgam h.le) α β) ?_ (qv_le_normalizer_usup h hαβ) ?_ ?_
  · omega
  ·
    intro α' hc _
    have hα' := hc.isMVtx_right _ h.hyp20
    have hc' := ms22_iii _ h.hyp20 hb0 hC hc
    refine ⟨XM _ α', le_rfl, by rw [hXM α' hα']; exact hc'.2.2, fun Y hY _ => ?_⟩
    rw [hXM α hα, hXM α' hα']
    refine le_sup_of_le_left ?_
    rw [critR_eq_usup_of_card h hφ hC hc
      (hq' α' _ hα' (adj_geo_one_of_isCritical _ hb0 hc')), Usup, zv_of_isMVtx _ hα',
      Subgroup.commutator_comm]
    exact Subgroup.commutator_mono le_rfl hY
  ·
    refine not_stab_le_normalizer_of_le_uloc h hφ hα ?_ (usup_ne_bot h hφ hC hα hαβ) ?_
    · rw [usup_eq_commutator_uloc h hfull hα hαβ]
      exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((qv_le_stab_of_adj _ hαβ.symm).trans (stab_le_normalizer_uloc h α))
    · rw [hq]
      have : 1 < Fintype.card F := by
        rw [← Nat.card_eq_fintype_card]
        exact Finite.one_lt_card
      calc Fintype.card F = Fintype.card F ^ 1 := (pow_one _).symm
        _ < Fintype.card F ^ 3 := Nat.pow_lt_pow_right this (by norm_num)
  ·
    intro δ' hc hgeo
    rw [hXM α hα, hXM δ' (hc.isMVtx_right _ h.hyp20)]
    have hZ : ZM (puAmalgam h.le) δ' ≤ Qv _ β := by
      rw [← hgeo]
      exact zm_le_qv_geo_one _ h.hyp20 hb0 hc
    have hle : ⁅ZM (puAmalgam h.le) α, ZM _ δ'⁆ ≤ Usup (puAmalgam h.le) α β := by
      rw [Usup, zv_of_isMVtx _ hα]
      exact Subgroup.commutator_mono le_rfl hZ
    have hR : ⁅ZM (puAmalgam h.le) α, ZM _ δ'⁆ = ⁅Uloc h.le L α, ZM _ δ'⁆ :=
      commutator_zm_eq_uloc h hfull hα (hZ.trans (qv_le_stab_of_adj _ hαβ.symm))
    have hne : ⁅Uloc h.le L α, ZM (puAmalgam h.le) δ'⁆ ≠ ⊥ := by
      rw [← hR]
      exact ms22_ii _ h.hyp20 hb0 hC hc
    have hcard := le_card_commutator_uloc h hφ hα hαβ hZ hne
    rw [← hR] at hcard
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hq]; exact hcard)).ge

end Card


section Normal

variable {G : Type*} [Group G]

theorem conjCl_le_of_le_normalizer {H K N : Subgroup G} (hKN : K ≤ N)
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) : conjCl H K ≤ N :=
  iSup₂_le fun _ hg => (Subgroup.map_mono hKN).trans
    (map_conj_eq_of_mem_normalizer (hHN hg)).le

end Normal

section Crit

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
include h hφ

theorem not_commutator_conjCl_le_zm (hC : CentHyp (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ¬ ⁅conjCl (stab _ α) (ZM (puAmalgam h.le) (geo _ α α' 2)), ZM _ α'⁆ ≤ ZM _ α := by
  intro hle
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hβ := adj_geo_one_of_isCritical _ hb0 hc
  have hZ' : ZM (puAmalgam h.le) α' ≤ Qv _ (geo _ α α' 1) := zm_le_qv_geo_one _ h.hyp20 hb0 hc
  have hZ'Q : ¬ ZM (puAmalgam h.le) α' ≤ Qv _ α := (ms22_iii _ h.hyp20 hb0 hC hc).2.2
  have hL := S46.commutator_ltil_le_of_commutator_le h hfull hα hβ
    (le_normalizer_conjCl _ _) (stab_le_normalizer_zm _ α) hle hZ' hZ'Q
  have hγL : ⁅ZM (puAmalgam h.le) (geo _ α α' 2), Ltil h.le L α⁆ ≤ ZM _ α :=
    (Subgroup.commutator_mono (le_conjCl _ _) le_rfl).trans hL
  have hd2 : (puAmalgam h.le).treeGraph.dist α (geo _ α α' 2) = 2 := by
    have := two_le_critDist _ h.hyp20 hb0
    exact dist_geo _ (by rw [hc.2.1]; omega)
  apply ms22_v _ h.hyp20 hb0 hC hV hc
  rw [xm_eq_zm h hfull hα, stab_eq_ltil_sup_qv h hfull hα]
  refine sup_le (le_normalizer_sup_of_commutator_le
    ((ltil_le_stab h α).trans (stab_le_normalizer_zm _ α)) (hγL.trans le_sup_right)) ?_
  refine le_normalizer_sup ?_ ((qv_le_stab _ α).trans (stab_le_normalizer_zm _ α))
  exact (qv_le_stab_of_dist_le_two _ h.hyp20 hα hd2.le).trans (stab_le_normalizer_zm _ _)

theorem commutator_conjCl_le_dloc_of_le (hC : CentHyp (puAmalgam h.le))
    (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (h441 : Concl441 h.le L α' (geo _ α' α 2)) {X : Subgroup (puAmalgam h.le).Universal}
    (hXV : X ≤ Vv (puAmalgam h.le) α) (hXQ : X ≤ Qv _ (geo _ α' α 2)) :
    ⁅conjCl (stab _ (geo _ α' α 2)) (ZM (puAmalgam h.le) α'), X⁆ ≤
      Dloc h.le L (geo _ α' α 2) := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have hb0 := h.critDist_pos
  have hα := hc.1
  have hα' := hc.isMVtx_right _ h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist α α' = critDist (puAmalgam h.le) := hc.2.1
  have hγe : geo (puAmalgam h.le) α' α 2 = geo _ α α' (critDist (puAmalgam h.le) - 2) := by
    have := geo_symm (puAmalgam h.le) (u := α) (w := α')
      (i := critDist (puAmalgam h.le) - 2) (by omega)
    rwa [hd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 2) = 2 by omega]
      at this
  have hρe : geo (puAmalgam h.le) α' α 3 = geo _ α α' (critDist (puAmalgam h.le) - 3) := by
    have := geo_symm (puAmalgam h.le) (u := α) (w := α')
      (i := critDist (puAmalgam h.le) - 3) (by omega)
    rwa [hd, show critDist (puAmalgam h.le) - (critDist (puAmalgam h.le) - 3) = 3 by omega]
      at this
  have hd' : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm]; exact hd
  set γ := geo (puAmalgam h.le) α' α 2 with hγdef
  have hγ : IsMVtx (puAmalgam h.le) γ :=
    (isMVtx_geo _ (by omega)).mpr ⟨fun _ => by decide, fun _ => hα'⟩
  have hγρ : (puAmalgam h.le).treeGraph.Adj γ (geo _ α' α 3) := adj_geo _ (by omega)
  have hdα'γ : (puAmalgam h.le).treeGraph.dist α' γ = 2 := dist_geo _ (by omega)
  have hdαρ : (puAmalgam h.le).treeGraph.dist α (geo _ α' α 3) =
      critDist (puAmalgam h.le) - 3 := by
    rw [hρe]; exact dist_geo _ (by omega)
  have hdβγ : (puAmalgam h.le).treeGraph.dist (geo _ α α' 1) γ =
      critDist (puAmalgam h.le) - 3 := by
    rw [show γ = geo (puAmalgam h.le) α α' (critDist (puAmalgam h.le) - 2) from hγe,
      dist_geo_geo _ (by omega) (by omega)]
    omega
  have hZs : ZM (puAmalgam h.le) α' ≤ stab _ γ :=
    (zm_le_qv_of_dist_lt _ hα' (by omega)).trans (qv_le_stab _ γ)
  have hDn := stab_le_normalizer_dloc h γ
  by_cases hH : ⁅ZM (puAmalgam h.le) α', Qv _ γ⁆ ≤ Dloc h.le L γ
  · exact (Subgroup.commutator_mono le_rfl hXQ).trans (commutator_conjCl_le hDn
      (stab_le_normalizer_qv _ γ) (hZs.trans hDn) hH)
  obtain ⟨-, h2⟩ := h441 hH
  rw [Subgroup.commutator_le]
  intro v hv x hx
  by_contra hvx
  have hnot : ¬ ⁅conjCl (stab _ γ) (ZM (puAmalgam h.le) α'), Subgroup.zpowers x⁆ ≤
      Dloc h.le L γ := fun hle =>
    hvx (hle (Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers x)))
  have hZγ := h2 x (hXQ hx) hnot
  set V' := conjCl (stab (puAmalgam h.le) γ) (ZM (puAmalgam h.le) α') with hV'
  set C := ⁅Subgroup.zpowers x, V'⁆ with hCdef
  have hV'γ : V' ≤ Vv (puAmalgam h.le) γ :=
    conjCl_le_of_le_normalizer (by
        rw [← zv_of_isMVtx _ hα']
        exact zv_le_vv h (by rw [SimpleGraph.dist_comm]; exact hdα'γ.le))
      (stab_le_normalizer_vv h γ)
  have hβ := adj_geo_one_of_isCritical _ hb0 hc
  have hV'α : V' ≤ stab (puAmalgam h.le) α :=
    hV'γ.trans ((vv_le_qv_of_dist h hγ (ρ := geo _ α α' 1)
      (by rw [SimpleGraph.dist_comm, hdβγ]; omega)).trans (qv_le_stab_of_adj _ hβ.symm))
  have hCα : C ≤ Vv (puAmalgam h.le) α := by
    rw [hCdef, Subgroup.commutator_le]
    intro g hg w hw
    have hgV : g ∈ Vv (puAmalgam h.le) α := (Subgroup.zpowers_le.mpr (hXV hx)) hg
    rw [commutatorElement_def]
    have : w * g⁻¹ * w⁻¹ ∈ Vv (puAmalgam h.le) α :=
      (stab_le_normalizer_vv h α (hV'α hw) _).mp ((Vv _ α).inv_mem hgV)
    simpa [mul_assoc] using (Vv _ α).mul_mem hgV this
  have hCγ : C ≤ stab (puAmalgam h.le) γ := by
    rw [hCdef, Subgroup.commutator_le]
    intro g hg w hw
    have hg' : g ∈ stab (puAmalgam h.le) γ :=
      Subgroup.zpowers_le.mpr ((hXQ.trans (qv_le_stab _ γ)) hx) hg
    have hw' : w ∈ stab (puAmalgam h.le) γ := conjCl_le_of_le hZs hw
    rw [commutatorElement_def]
    exact (stab _ γ).mul_mem ((stab _ γ).mul_mem ((stab _ γ).mul_mem hg' hw')
      ((stab _ γ).inv_mem hg')) ((stab _ γ).inv_mem hw')
  obtain ⟨ρ₀, hdρ₀, hρ₀⟩ : ∃ ρ₀, (puAmalgam h.le).treeGraph.dist α ρ₀ ≤ 2 ∧
      ¬ Zv (puAmalgam h.le) ρ₀ ≤ Qv _ γ := by
    by_contra hall
    push Not at hall
    exact hV α α' hc (iSup₂_le fun ρ₀ hρ₀ => hall ρ₀ hρ₀)
  obtain ⟨μ, hμ, hdμ, hρμ⟩ := exists_zv_le_zm h hα hdρ₀
  have hμγ : ¬ ZM (puAmalgam h.le) μ ≤ Qv _ γ := fun hle => hρ₀ (hρμ.trans hle)
  have hμV : ZM (puAmalgam h.le) μ ≤ Vv _ α := by
    rw [← zv_of_isMVtx _ hμ]; exact zv_le_vv h hdμ
  have hμρ : ZM (puAmalgam h.le) μ ≤ Qv _ (geo _ α' α 3) := by
    refine zm_le_qv_of_dist_lt _ hμ ?_
    have := dist_triangle _ μ α (geo _ α' α 3)
    rw [tdist_comm _ μ α] at this
    omega
  have hμs : ZM (puAmalgam h.le) μ ≤ stab _ γ := hμρ.trans (qv_le_stab_of_adj _ hγρ.symm)
  have hab := vv_comm_eq_bot h hb hα
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hab
  have hcent : ZM (puAmalgam h.le) μ ≤
      Subgroup.centralizer (Uloc h.le L γ : Set (puAmalgam h.le).Universal) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huZ : u ∈ (((C ⊔ Dloc h.le L γ : Subgroup _) : Set (puAmalgam h.le).Universal)) :=
      hZγ (uloc_le_zm h hfull hγ hu)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hCγ.trans hDn)] at huZ
    obtain ⟨c, hcC, d, hdD, rfl⟩ := huZ
    have hzc : z * c = c * z :=
      (Subgroup.mem_centralizer_iff.mp (hab (hμV hz)) c (hCα hcC)).symm
    have hzs := hμs hz
    set e := (c * d)⁻¹ * (z * (c * d) * z⁻¹) with he
    have heU : e ∈ Uloc h.le L γ :=
      (Uloc h.le L γ).mul_mem ((Uloc h.le L γ).inv_mem hu)
        ((stab_le_normalizer_uloc h γ hzs _).mp hu)
    have heD : e ∈ Dloc h.le L γ := by
      have e2 : e = d⁻¹ * (z * d * z⁻¹) := by
        rw [he]
        calc (c * d)⁻¹ * (z * (c * d) * z⁻¹) = d⁻¹ * c⁻¹ * ((z * c) * d * z⁻¹) := by group
          _ = d⁻¹ * (z * d * z⁻¹) := by rw [hzc]; group
      rw [e2]
      exact (Dloc h.le L γ).mul_mem ((Dloc h.le L γ).inv_mem hdD) ((hDn hzs _).mp hdD)
    have he1 : e = 1 := by
      have := uloc_inf_dloc h hφ γ
      rw [← Subgroup.mem_bot, ← this]
      exact ⟨heU, heD⟩
    rw [he, inv_mul_eq_one] at he1
    calc c * d * z = z * (c * d) * z⁻¹ * z := by rw [← he1]
      _ = z * (c * d) := by group
  apply hμγ
  rw [← hC γ _ hγ hγρ]
  intro z hz
  exact ⟨hμρ hz, (mem_centralizer_zm_iff h hfull hγ (hμs hz)).mpr (hcent hz)⟩

theorem critR_le_dloc (hC : CentHyp (puAmalgam h.le)) (hb : 4 < critDist (puAmalgam h.le))
    (hV : ∀ δ δ' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) δ δ' →
      ¬ Vv (puAmalgam h.le) δ ≤ Qv _ (geo _ δ' δ 2))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (h441 : Concl441 h.le L α' (geo _ α' α 2)) :
    ⁅ZM (puAmalgam h.le) α, ZM _ α'⁆ ≤ Dloc h.le L (geo _ α' α 2) := by
  have hd : (puAmalgam h.le).treeGraph.dist α' α = critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm]; exact hc.2.1
  have hdγ : (puAmalgam h.le).treeGraph.dist α (geo _ α' α 2) =
      critDist (puAmalgam h.le) - 2 := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd]
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono (le_conjCl _ _) le_rfl).trans
    (commutator_conjCl_le_dloc_of_le h hφ hC hb hV hc h441 (zm_le_vv h hc.1)
      (zm_le_qv_of_dist_lt _ hc.1 (by omega)))

end Crit

end CFSG.Quasithin.MS93.S4A

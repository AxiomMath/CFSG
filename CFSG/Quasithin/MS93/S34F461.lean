module

public import CFSG.Quasithin.MS93.S34FLin
public import CFSG.Quasithin.MS93.S34FGen
public import CFSG.Quasithin.MS93.S34FCore
public import CFSG.Quasithin.MS93.S46Crit
import CFSG.Quasithin.MS93.S46TypeLin

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Center

variable (h : PUHyp M T L)
include h

theorem stab_le_normalizer_centerOf (α : Vtx (puAmalgam h.le)) :
    stab _ α ≤ Subgroup.normalizer (centerOf (Vv (puAmalgam h.le) α) : Set _) := by
  refine le_normalizer_of_map_conj_le fun g hg => ?_
  rw [← PU.centerOf_map (MulAut.conj g).injective,
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_vv h α hg)]

theorem zm_le_centerOf (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) : ZM (puAmalgam h.le) α ≤ centerOf (Vv _ α) :=
  le_inf (zm_le_vv h hα) ((zm_le_centralizer_qv _ h.hyp20 hα).trans
    (Subgroup.centralizer_le (vv_le_qv h hb hα)))

theorem commutator_zm_eq_commutator_uloc_of_le_qv {δ ρ : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) (hδρ : (puAmalgam h.le).treeGraph.Adj δ ρ)
    {K : Subgroup (puAmalgam h.le).Universal} (hK : K ≤ Qv _ ρ) :
    ⁅ZM (puAmalgam h.le) δ, K⁆ = ⁅Uloc h.le L δ, K⁆ := by
  have hZab : ZM (puAmalgam h.le) δ ≤ Subgroup.centralizer (ZM (puAmalgam h.le) δ : Set _) :=
    (Subgroup.le_centralizer_iff_isMulCommutative).mpr
      (isElemAbelian_zm _ h.hyp20 h.critDist_pos hδ).1
  rw [zm_eq_zh_sup_uloc h hδ hδρ]
  exact commutator_sup_eq_of_le_centralizer
    (((zh_le_zm _ hδρ).trans hZab).trans (Subgroup.centralizer_le (uloc_le_zm' h hδ)))
    ((zh_le_centralizer _ ρ).trans (Subgroup.centralizer_le hK))

end Center

section Crit

variable (h : PUHyp M T L) (hC : CentHyp (puAmalgam h.le))
include hC

theorem critR_eq_commutator_uloc_right {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α') :
    critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ ∧
      critR (puAmalgam h.le) α α' ≤ Uloc h.le L α' ⊓ ZM (puAmalgam h.le) α := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  have hα'ε := adj_geo_one_of_isCritical _ hb hc'
  have hZε : ZM (puAmalgam h.le) α ≤ Qv _ (geo _ α' α 1) :=
    zm_le_qv_geo_one_left _ h.hyp20 hb hC hc
  have hZs : ZM (puAmalgam h.le) α ≤ stab _ α' := hZε.trans (qv_le_stab_of_adj _ hα'ε.symm)
  have heq : critR (puAmalgam h.le) α α' = ⁅Uloc h.le L α', ZM (puAmalgam h.le) α⁆ := by
    rw [critR, Subgroup.commutator_comm,
      commutator_zm_eq_commutator_uloc_of_le_qv h hc'.1 hα'ε hZε]
  refine ⟨heq, le_inf ?_ ?_⟩
  · rw [heq]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hZs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α'))
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((zm_le_stab_of_isCritical _ h.hyp20 hb hc).trans (stab_le_normalizer_zm _ α))

theorem centerOf_vv_le_qv_end (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    centerOf (Vv (puAmalgam h.le) α) ≤ Qv _ (geo _ α' α 1) := by
  have hγ : IsMVtx _ (geo (puAmalgam h.le) α α' 2) := S46.isMVtx_geo_two' hb4 hc
  have hNγ := S46.centerOf_vv_le_qv h.hyp20 hC (by omega) hc.1 hγ
    (S46.dist_geo_crit hb4 hc (by omega))
  have hγε : (puAmalgam h.le).treeGraph.Adj (geo _ α α' 2) (geo _ α' α 1) := by
    rw [S46.geo_rev_one hb4 hc]
    exact S46.adj_geo_crit hb4 hc (by omega)
  exact hNγ.trans (qv_le_qv _ h.hyp20 hγ hγε)

theorem commutator_centerOf_zm_le_gen (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    ⁅centerOf (Vv (puAmalgam h.le) α), ZM _ α'⁆ ≤
      Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hc' := ms22_iii _ h.hyp20 hb0 hC hc
  have hα'ε := adj_geo_one_of_isCritical _ hb0 hc'
  have hNε := centerOf_vv_le_qv_end h hC hb4 hc
  have hNs : centerOf (Vv (puAmalgam h.le) α) ≤ stab _ α' :=
    hNε.trans (qv_le_stab_of_adj _ hα'ε.symm)
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm, commutator_zm_eq_commutator_uloc_of_le_qv h hc'.1 hα'ε hNε]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp
      (hNs.trans (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α'))
  · have h1 : ⁅centerOf (Vv (puAmalgam h.le) α), ZM _ α'⁆ ≤ centerOf (Vv _ α) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((zm_le_stab_of_isCritical _ h.hyp20 hb0 hc).trans (stab_le_normalizer_centerOf h α))
    exact h1.trans (inf_le_right.trans (Subgroup.centralizer_le (zm_le_vv h hc.1)))

theorem centerOf_vv_le_bloc_of_commutator_le_gen (hb : 2 < critDist (puAmalgam h.le))
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ⁅centerOf (Vv (puAmalgam h.le) α), ZM _ α'⁆ ≤ ZM _ α) :
    centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α := by
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have hβ := adj_geo_one_of_isCritical _ hb0 hc
  have hc' := ms22_iii _ h.hyp20 hb0 hC hc
  have hL := commutator_ltil_le_of_commutator_le_gen h hc.1 hβ
    (stab_le_normalizer_centerOf h α) (stab_le_normalizer_zm _ α) hN
    (zm_le_qv_geo_one _ h.hyp20 hb0 hc) hc'.2.2
  intro x hx
  rw [mem_bloc_iff h hb hc.1]
  exact ⟨hx.1, fun l hl => hL (Subgroup.commutator_mem_commutator hx hl)⟩

end Crit

section Flat

variable (h : PUHyp M T L) (hU : IsSL3U M T L) (hC : CentHyp (puAmalgam h.le))
include hU hC

theorem centerOf_vv_le_flat (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α') :
    centerOf (Vv (puAmalgam h.le) α) ≤ Qv _ (geo _ α' α 1) ⊓ flat h α' := by
  have hNε := centerOf_vv_le_qv_end h hC hb4 hc
  have hNR : centerOf (Vv (puAmalgam h.le) α) ≤
      Subgroup.centralizer (critR (puAmalgam h.le) α α' : Set _) :=
    inf_le_right.trans (Subgroup.centralizer_le
      (((critR_eq_commutator_uloc_right h hC hc).2.trans inf_le_right).trans (zm_le_vv h hc.1)))
  exact le_inf hNε ((le_inf hNε hNR).trans (qv_inf_centralizer_critR_le_flat h hU hc))

theorem uloc_inf_centralizer_eq_critR_flat {α α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) α α')
    (hne : (Qv (puAmalgam h.le) α').relIndex (ZM (puAmalgam h.le) α) ≠
      Nat.card ↥(critR (puAmalgam h.le) α α')) :
    Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) =
      critR (puAmalgam h.le) α α' := by
  have hb := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb hC hc
  obtain ⟨n, F, _, _, φ, hcard, hφs, hφ⟩ := exists_natural_flat h hU
  obtain ⟨ψ, -, hψ⟩ := exists_natural_flat_at h hφs hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_flat_at h hφs hφ hc'.1
  obtain ⟨hf, -, hrel, hR, hwf, -⟩ := s35_core_flat h hU hC hcard hc hψ hψ'
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  set f := Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) with hfdef
  set w := Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) with hwdef
  have hw1 : w ≠ 0 := by
    intro hw0
    have hRne : critR (puAmalgam h.le) α α' ≠ ⊥ := ms22_ii _ h.hyp20 hb hC hc
    apply hRne
    rw [← Subgroup.card_eq_one, hR, hw0, pow_zero]
  have hf2 : f ≤ 2 := by
    by_contra hcon
    apply hc.2.2
    rw [← Subgroup.relIndex_eq_one, hrel, show 3 - f = 0 by omega, pow_zero]
  have hwf' : w = f := by
    by_contra hne'
    apply hne
    rw [hrel, hR, show 3 - f = 1 by omega, show w = 1 by omega]
  obtain ⟨hReq, hRle⟩ := critR_eq_commutator_uloc_right h hC hc
  have hRW : critR (puAmalgam h.le) α α' ≤
      Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) :=
    le_inf (hRle.trans inf_le_left) ((hRle.trans inf_le_right).trans
      ((Subgroup.le_centralizer_iff_isMulCommutative).mpr
        (isElemAbelian_zm _ h.hyp20 hb hc.1).1))
  have hcardW : Nat.card ↥(Uloc h.le L α' ⊓
      Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _)) = Nat.card F ^ f := by
    rw [card_inf_centralizer_eq hψ' (zm_le_flat h hU hc), card_fixN, hf]
  have : Finite ↥(Uloc h.le L α') := Finite.of_equiv _ (natCoord hψ').toEquiv.symm
  have : Finite ↥(Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
  exact (Subgroup.eq_of_le_of_card_ge hRW (by rw [hcardW, hR, hwf'])).symm

theorem commutator_zm_flat_le_centerOf (hb4 : critDist (puAmalgam h.le) = 4)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α α')
    (hN : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅ZM (puAmalgam h.le) α', Qv _ (geo _ α' α 1) ⊓ flat h α'⁆ ≤ centerOf (Vv _ α) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  have h20 := h.hyp20
  have hc' := ms22_iii _ h20 hb0 hC hc
  have hα'ε := adj_geo_one_of_isCritical _ hb0 hc'
  have hεH : ¬ IsMVtx (puAmalgam h.le) (geo _ α' α 1) := by
    rw [← isMVtx_iff_of_adj _ hα'ε]
    exact hc'.1
  obtain ⟨n, F, _, _, φ, hcard, hφs, hφ⟩ := exists_natural_flat h hU
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  obtain ⟨ψ, -, hψ⟩ := exists_natural_flat_at h hφs hφ hc.1
  obtain ⟨ψ', -, hψ'⟩ := exists_natural_flat_at h hφs hφ hc'.1
  obtain ⟨hf, -, hrel, hR, hwf, -⟩ := s35_core_flat h hU hC hcard hc hψ hψ'
  set N := centerOf (Vv (puAmalgam h.le) α) with hNdef
  set Y := Qv (puAmalgam h.le) (geo _ α' α 1) ⊓ flat h α' with hYdef
  set f := Module.finrank F (fixN (natImage ψ (ZM (puAmalgam h.le) α'))) with hfdef
  set w := Module.finrank F (commN (natImage ψ (ZM (puAmalgam h.le) α'))) with hwdef
  have hw1 : w ≠ 0 := by
    intro hw0
    have hRne : critR (puAmalgam h.le) α α' ≠ ⊥ := ms22_ii _ h20 hb0 hC hc
    apply hRne
    rw [← Subgroup.card_eq_one, hR, hw0, pow_zero]
  have hf2 : f ≤ 2 := by
    by_contra hcon
    apply hc.2.2
    rw [← Subgroup.relIndex_eq_one, hrel, show 3 - f = 0 by omega, pow_zero]
  have hNY : N ≤ Y := centerOf_vv_le_flat h hU hC hb4 hc
  have hNε : N ≤ Qv _ (geo _ α' α 1) := hNY.trans inf_le_left
  have hYε : Y ≤ Qv _ (geo _ α' α 1) := inf_le_left
  have hcardN : Nat.card ↥⁅Uloc h.le L α', N⁆ =
      Nat.card F ^ Module.finrank F (commN (natImage ψ' N)) := by
    rw [card_commutator_eq hψ' (hNY.trans inf_le_right), Module.natCard_eq_pow_finrank (K := F)]
  have hcardY : Nat.card ↥⁅Uloc h.le L α', Y⁆ =
      Nat.card F ^ Module.finrank F (commN (natImage ψ' Y)) := by
    rw [card_commutator_eq hψ' inf_le_right, Module.natCard_eq_pow_finrank (K := F)]
  have hY2 : IsPGroup 2 ↥(natImage ψ' Y) := by
    have hP : IsPGroup 2 ↥Y := (isPGroup_qv _ h20 hεH).to_le inf_le_left
    exact (hP.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm).map _
  have hdY := S46.finrank_commN_le_two_of_pGroup hY2
  obtain ⟨hReq, hRle⟩ := critR_eq_commutator_uloc_right h hC hc
  have hRN : critR (puAmalgam h.le) α α' ≤ ⁅Uloc h.le L α', N⁆ := by
    rw [hReq]
    exact Subgroup.commutator_mono le_rfl (zm_le_centerOf h hb hc.1)
  have hUN : ⁅Uloc h.le L α', N⁆ = ⁅N, ZM (puAmalgam h.le) α'⁆ := by
    rw [← commutator_zm_eq_commutator_uloc_of_le_qv h hc'.1 hα'ε hNε, Subgroup.commutator_comm]
  have hNW : ⁅Uloc h.le L α', N⁆ ≤
      Uloc h.le L α' ⊓ Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) := by
    rw [hUN]
    exact commutator_centerOf_zm_le_gen h hC hb4 hc
  have hcardW : Nat.card ↥(Uloc h.le L α' ⊓
      Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _)) = Nat.card F ^ f := by
    rw [card_inf_centralizer_eq hψ' (zm_le_flat h hU hc), card_fixN, hf]
  have : Finite ↥(Uloc h.le L α') := Finite.of_equiv _ (natCoord hψ').toEquiv.symm
  have hUfin : ∀ K : Subgroup (puAmalgam h.le).Universal, K ≤ Uloc h.le L α' → Finite ↥K :=
    fun K hK => Finite.of_injective _ (Subgroup.inclusion_injective hK)
  have hNU : ⁅Uloc h.le L α', N⁆ ≤ Uloc h.le L α' := hNW.trans inf_le_left
  have hYU : ⁅Uloc h.le L α', Y⁆ ≤ Uloc h.le L α' :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((hYε.trans (qv_le_stab_of_adj _ hα'ε.symm)).trans
        (stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) α'))
  have := hUfin _ hNU
  have := hUfin _ hYU
  have := hUfin _ (inf_le_left : Uloc h.le L α' ⊓
    Subgroup.centralizer (ZM (puAmalgam h.le) α : Set _) ≤ Uloc h.le L α')
  set d := Module.finrank F (commN (natImage ψ' N)) with hddef
  have hwd : w ≤ d := by
    have := Subgroup.card_le_of_le hRN
    rw [hR, hcardN] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hdf : d ≤ f := by
    have := Subgroup.card_le_of_le hNW
    rw [hcardN, hcardW] at this
    exact (Nat.pow_le_pow_iff_right hq).mp this
  have hdw : d ≠ w := by
    intro hdw
    apply hN
    refine centerOf_vv_le_bloc_of_commutator_le_gen h hC hb hc ?_
    have heqR : ⁅Uloc h.le L α', N⁆ = critR (puAmalgam h.le) α α' :=
      (Subgroup.eq_of_le_of_card_ge hRN (by rw [hcardN, hR, hdw])).symm
    rw [← hUN, heqR]
    exact hRle.trans inf_le_right
  have hd2 : d = 2 := by omega
  have hNYc : ⁅Uloc h.le L α', N⁆ ≤ ⁅Uloc h.le L α', Y⁆ := Subgroup.commutator_mono le_rfl hNY
  have heqY : ⁅Uloc h.le L α', N⁆ = ⁅Uloc h.le L α', Y⁆ := by
    refine Subgroup.eq_of_le_of_card_ge hNYc ?_
    rw [hcardN, hcardY, hd2]
    exact Nat.pow_le_pow_right (by omega) hdY
  rw [commutator_zm_eq_commutator_uloc_of_le_qv h hc'.1 hα'ε hYε, ← heqY, hUN]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((zm_le_stab_of_isCritical _ h20 hb0 hc).trans (stab_le_normalizer_centerOf h α))

theorem commutator_vv_inf_qv_le_centerOf_flat (hb4 : critDist (puAmalgam h.le) = 4)
    {α δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) α δ)
    (hN : ¬ centerOf (Vv (puAmalgam h.le) α) ≤ Bloc h.le L α) :
    ⁅Vv (puAmalgam h.le) α ⊓ Qv _ (geo _ α δ 2), ZM _ δ⁆ ≤ centerOf (Vv _ α) := by
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hγ : IsMVtx _ (geo (puAmalgam h.le) α δ 2) := S46.isMVtx_geo_two' hb4 hc
  have hγε : (puAmalgam h.le).treeGraph.Adj (geo _ α δ 2) (geo _ δ α 1) := by
    rw [S46.geo_rev_one hb4 hc]
    exact S46.adj_geo_crit hb4 hc (by omega)
  have hVε : Vv (puAmalgam h.le) α ⊓ Qv _ (geo _ α δ 2) ≤ Qv _ (geo _ δ α 1) :=
    inf_le_right.trans (qv_le_qv _ h.hyp20 hγ hγε)
  have hVR : Vv (puAmalgam h.le) α ≤
      Subgroup.centralizer (critR (puAmalgam h.le) α δ : Set _) := by
    refine Subgroup.centralizer_le ((critR_eq_commutator_uloc_right h hC hc).2.trans
      inf_le_right) |>.trans' ?_
    rw [Subgroup.le_centralizer_iff]
    exact (zm_le_centerOf h hb hc.1).trans inf_le_right
  have hVflat : Vv (puAmalgam h.le) α ⊓ Qv _ (geo _ α δ 2) ≤ Qv _ (geo _ δ α 1) ⊓ flat h δ :=
    le_inf hVε ((le_inf hVε (inf_le_left.trans hVR)).trans
      (qv_inf_centralizer_critR_le_flat h hU hc))
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono le_rfl hVflat).trans
    (commutator_zm_flat_le_centerOf h hU hC hb4 hc hN)

end Flat

end CFSG.Quasithin.MS93.S34F

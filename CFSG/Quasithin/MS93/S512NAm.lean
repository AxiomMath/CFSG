module

public import CFSG.Quasithin.MS93.S310MI

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem inf_bSub_sup_le (h : PUHyp M T L) {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    ZM _ ρ ⊓ S5.bSub h.le L δ ⊔ ZM _ δ ≤ S5.bSub h.le L δ :=
  sup_le inf_le_right (S310.zm_le_bSub h hδ)

theorem le_normalizer_inf_bSub_sup (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hd : (puAmalgam h.le).treeGraph.dist δ ρ = 2) :
    stab _ δ ≤ Subgroup.normalizer
      ((ZM _ ρ ⊓ S5.bSub h.le L δ ⊔ ZM _ δ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
  set Y : Subgroup (puAmalgam h.le).Universal := ZM _ ρ ⊓ S5.bSub h.le L δ ⊔ ZM _ δ with hY
  have hadj : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ ρ 1) := adj_geo_one _ (by omega)
  have hadj' : (puAmalgam h.le).treeGraph.Adj (geo _ δ ρ 1) ρ := by
    have := adj_geo _ (u := δ) (w := ρ) (i := 1) (by omega)
    rwa [show 1 + 1 = 2 from rfl, ← hd, geo_dist] at this
  have hL : ∀ l ∈ puTrans h.le L δ, Y.map (MulAut.conj l).toMonoidHom ≤ Y := by
    intro l hl
    rintro _ ⟨y, hy, rfl⟩
    have hyB : y ∈ S5.bSub h.le L δ := inf_bSub_sup_le h hδ hy
    have hc : ⁅y, l⁆ ∈ ZM _ δ := S5B.commutator_mem_zm_of_mem_bSub h hb hδ hyB hl
    have e : (MulAut.conj l).toMonoidHom y = ⁅y, l⁆⁻¹ * y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Y.mul_mem (Subgroup.mem_sup_right (inv_mem hc)) hy
  have hT : Qv _ (geo _ δ ρ 1) ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal) := by
    have hTρ : Qv _ (geo _ δ ρ 1) ≤ stab _ ρ := qv_le_stab_of_adj _ hadj'
    have hTδ : Qv _ (geo _ δ ρ 1) ≤ stab _ δ := qv_le_stab_of_adj _ hadj.symm
    exact le_normalizer_sup (le_normalizer_inf (hTρ.trans (stab_le_normalizer_zm _ _))
      (hTδ.trans (S310.stab_le_normalizer_bSub h δ))) (hTδ.trans (stab_le_normalizer_zm _ _))
  intro g hg
  obtain ⟨l, hl, t, ht, rfl⟩ := S310.exists_puTrans_mul_of_isMVtx h hδ hadj hg
  refine mul_mem ?_ (hT ht)
  exact mem_normalizer_of_map_conj_le (hL l hl) (hL l⁻¹ (inv_mem hl))

theorem inf_bSub_sup_smul (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hd : (puAmalgam h.le).treeGraph.dist δ ρ = 2) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ δ) :
    ZM _ (g • ρ) ⊓ S5.bSub h.le L δ ⊔ ZM _ δ = ZM _ ρ ⊓ S5.bSub h.le L δ ⊔ ZM _ δ := by
  have hY := map_conj_eq_of_mem_normalizer (le_normalizer_inf_bSub_sup h hb hδ hd hg)
  rw [← hY, Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← zm_smul,
    map_conj_eq_of_mem_normalizer (S310.stab_le_normalizer_bSub h δ hg),
    map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ _ hg)]

theorem zm_le_qv_two (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    (hd : (puAmalgam h.le).treeGraph.dist δ ρ = 2) : ZM _ ρ ≤ Qv _ δ :=
  zm_le_qv_of_dist_lt _ hρ (by rw [SimpleGraph.dist_comm, hd]; exact hb)

theorem inf_bSub_sup_le_centralizer_smul (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hρ : IsMVtx _ ρ)
    (hd : (puAmalgam h.le).treeGraph.dist δ ρ = 2) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ δ) :
    ZM _ ρ ⊓ S5.bSub h.le L δ ⊔ ZM _ δ ≤
      Subgroup.centralizer (ZM _ (g • ρ) : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hgρ : IsMVtx _ (g • ρ) := (isMVtx_smul _ _ _).2 hρ
  have hgd : (puAmalgam h.le).treeGraph.dist δ (g • ρ) = 2 := by
    have := dist_smul _ g δ ρ
    rw [(mem_stab _).1 hg] at this
    rw [this, hd]
  rw [← inf_bSub_sup_smul h hb hδ hd hg]
  refine sup_le (inf_le_left.trans ?_) ?_
  · exact Subgroup.le_centralizer_iff_isMulCommutative.mpr (isElemAbelian_zm _ hyp hb0 hgρ).1
  · exact (zm_le_centralizer_qv _ hyp hδ).trans
      (Subgroup.centralizer_le (zm_le_qv_two h hb hgρ hgd))

theorem inf_bSub_sup_le_centralizer_nclStab (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hρ : IsMVtx _ ρ) (hd : (puAmalgam h.le).treeGraph.dist δ ρ = 2) :
    ZM _ ρ ⊓ S5.bSub h.le L δ ⊔ ZM _ δ ≤
      Subgroup.centralizer (S5.nclStab _ δ (ZM _ ρ) : Set (puAmalgam h.le).Universal) := by
  rw [Subgroup.le_centralizer_iff]
  refine iSup_le fun g => ?_
  rw [← zm_smul]
  exact Subgroup.le_centralizer_iff.1
    (inf_bSub_sup_le_centralizer_smul h hb hδ hρ hd g.2)

theorem inf_bSub_le_qv (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ ρ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hρ : IsMVtx _ ρ)
    (hd : (puAmalgam h.le).treeGraph.dist δ ρ = 2) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ δ) : ZM _ (g • ρ) ⊓ S5.bSub h.le L δ ≤ Qv _ ρ := by
  have hb0 := h.critDist_pos
  refine le_sup_left.trans ((inf_bSub_sup_smul h hb hδ hd hg).le.trans (sup_le ?_ ?_))
  · exact inf_le_left.trans (zm_le_qv_self _ hρ hb0)
  · exact zm_le_qv_two h hb hδ (by rw [SimpleGraph.dist_comm, hd])

end S512N

end CFSG.Quasithin.MS93

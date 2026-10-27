module

public import CFSG.Quasithin.MS93.S5A55Lift
public import CFSG.Quasithin.MS93.S510Gp
public import CFSG.Quasithin.MS93.S510Path
public import CFSG.Quasithin.MS93.S5B512O5

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S510S2

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem puTrans_perfect (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    ⁅puTrans h.le L ρ, puTrans h.le L ρ⁆ = puTrans h.le L ρ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  rw [puTrans_smul h.le h.L_subgroupOf_normal, ← Subgroup.map_commutator,
    S38E.puTrans_baseA_perfect h]

theorem finite_puTrans (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    Finite ↥(puTrans h.le L ρ) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  rw [puTrans_smul h.le h.L_subgroupOf_normal]
  have := S5.finite_puTrans_baseA h
  exact Finite.of_surjective _
    (((MulAut.conj g).toMonoidHom).subgroupMap_surjective (puTrans h.le L (baseA _)))

theorem critR_le_commutator_uSub_gp (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    critR _ γ γ' ≤ ⁅S5.uSub h.le L γ, ZM _ γ'⁆ := by
  obtain ⟨g, rfl, -, hc', hβ'⟩ := S510.exists_base_crit h hc
  have key := S5B.critR_le_commutator_uSub h hb hc' hβ'
  have e1 : γ' = g • (g⁻¹ • γ') := (smul_inv_smul g γ').symm
  rw [e1, S510.critR_smul, S5B.uSub_smul h.le h.L_subgroupOf_normal, zm_smul,
    ← Subgroup.map_commutator, map_conj_le_map_conj_iff]
  exact key

theorem zm_le_stab_of_dist_le (h : PUHyp M T L) {γ δ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hd : (puAmalgam h.le).treeGraph.dist γ δ ≤ critDist (puAmalgam h.le)) :
    ZM _ γ ≤ stab _ δ := by
  have hb0 := h.critDist_pos
  rcases Nat.lt_or_ge ((puAmalgam h.le).treeGraph.dist γ δ) (critDist (puAmalgam h.le)) with
    hlt | hge
  · exact (zm_le_qv_of_dist_lt _ hγ hlt).trans (qv_le_stab _ _)
  · have hdδ : (puAmalgam h.le).treeGraph.dist δ γ = critDist (puAmalgam h.le) := by
      rw [tdist_comm]; omega
    have hadj : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ γ 1) := adj_geo_one _ (by omega)
    have hd1 : (puAmalgam h.le).treeGraph.dist γ (geo _ δ γ 1) < critDist (puAmalgam h.le) := by
      rw [tdist_comm, dist_geo_right _ (by omega), hdδ]
      omega
    exact (zm_le_qv_of_dist_lt _ hγ hd1).trans (qv_le_stab_of_adj _ hadj.symm)

end Vertex

end S510S2

end CFSG.Quasithin.MS93

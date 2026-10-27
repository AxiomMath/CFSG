module

public import CFSG.Quasithin.MS93.S512TBase
public import CFSG.Quasithin.MS93.S5B57

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512T

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem pair_facts (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    IsMVtx _ μ ∧ IsMVtx _ γ ∧ IsMVtx _ (geo _ μ γ 2) ∧
      (puAmalgam h.le).treeGraph.dist μ γ = 4 ∧
      (puAmalgam h.le).treeGraph.Adj μ (geo _ μ γ 1) ∧
      (puAmalgam h.le).treeGraph.Adj (geo _ μ γ 1) (geo _ μ γ 2) ∧
      (puAmalgam h.le).treeGraph.Adj (geo _ μ γ 2) (geo _ μ γ 3) ∧
      (puAmalgam h.le).treeGraph.Adj (geo _ μ γ 3) γ ∧
      (puAmalgam h.le).treeGraph.dist μ (geo _ μ γ 2) = 2 ∧
      (puAmalgam h.le).treeGraph.dist (geo _ μ γ 2) γ = 2 ∧
      (puAmalgam h.le).treeGraph.dist μ (geo _ μ γ 3) = 3 ∧
      (puAmalgam h.le).treeGraph.dist (geo _ μ γ 1) γ = 3 := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist μ γ = 4 := hc.2.1.trans hb4
  have h4 : geo _ μ γ 4 = γ := by
    have := geo_dist (puAmalgam h.le) μ γ
    rwa [hd] at this
  refine ⟨hc.1, hc.isMVtx_right _ hyp, isMVtx_geo_two _ hyp hb0 hc, hd, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact adj_geo_one _ (by omega)
  · exact adj_geo _ (i := 1) (by omega)
  · exact adj_geo _ (i := 2) (by omega)
  · have := adj_geo _ (u := μ) (w := γ) (i := 3) (by omega)
    rwa [h4] at this
  · exact dist_geo _ (by omega)
  · rw [dist_geo_right _ (by omega), hd]
  · exact dist_geo _ (by omega)
  · rw [dist_geo_right _ (by omega), hd]

theorem relIndex_qv_zm_eq (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    (Qv _ γ).relIndex (ZM _ μ) =
      (Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L μ) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨hμ, hγ, hα, -, hμρ, hρα, -, hσγ, -, hαγ, hμσ, -⟩ := pair_facts h hb4 hc
  have hZ := S5B.zm_eq_zh_sup_uSub h hμ hμρ
  have hZρ : ZH _ (geo _ μ γ 1) ≤ Qv _ γ :=
    (zh_le_zm _ hρα.symm).trans (zm_le_qv_of_dist_lt _ hα (by omega))
  have hab := (isElemAbelian_zm _ hyp hb0 hμ).1
  have hcomm : ∀ x ∈ ZM (puAmalgam h.le) μ, ∀ y ∈ ZM (puAmalgam h.le) μ, x * y = y * x := by
    intro x hx y hy
    have := hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  rw [hZ, sup_comm, relIndex_sup_of_le_of_comm (A := ZM _ μ) hcomm (S5B.uSub_le_zm h.le μ)
    (zh_le_zm _ hμρ) hZρ, ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (Subgroup.centralizer _)]
  congr 1
  apply le_antisymm
  · exact inf_le_inf_right _ (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγ))
  · rintro x ⟨hxc, hxU⟩
    refine ⟨?_, hxU⟩
    have hxσ : x ∈ Qv _ (geo _ μ γ 3) :=
      zm_le_qv_of_dist_lt _ hμ (by omega) (S5B.uSub_le_zm h.le μ hxU)
    rw [← h.centHyp γ (geo _ μ γ 3) hγ hσγ.symm]
    exact ⟨hxσ, hxc⟩

theorem uSub_inf_qv_eq (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    S5.uSub h.le L μ ⊓ Qv _ γ =
      S5.uSub h.le L μ ⊓ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  obtain ⟨hμ, hγ, -, -, -, -, -, hσγ, -, -, hμσ, -⟩ := pair_facts h hb4 hc
  apply le_antisymm
  · exact inf_le_inf_left _ (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγ))
  · rintro x ⟨hxU, hxc⟩
    refine ⟨hxU, ?_⟩
    have hxσ : x ∈ Qv _ (geo _ μ γ 3) :=
      zm_le_qv_of_dist_lt _ hμ (by omega) (S5B.uSub_le_zm h.le μ hxU)
    rw [← h.centHyp γ (geo _ μ γ 3) hγ hσγ.symm]
    exact ⟨hxσ, hxc⟩

theorem zm_facts (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    ZM _ γ ≤ Qv _ (geo _ μ γ 1) ∧ ZM _ γ ≤ stab _ μ ∧ IsPGroup 2 (ZM (puAmalgam h.le) γ) ∧
      ¬ ZM _ γ ≤ Qv _ μ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨hμ, hγ, -, -, hμρ, -, -, -, -, -, -, hργ⟩ := pair_facts h hb4 hc
  have hZρ : ZM _ γ ≤ Qv _ (geo _ μ γ 1) :=
    zm_le_qv_of_dist_lt _ hγ (by rw [SimpleGraph.dist_comm]; omega)
  have hρ : ¬ IsMVtx _ (geo _ μ γ 1) := (isMVtx_iff_of_adj _ hμρ).1 hμ
  exact ⟨hZρ, hZρ.trans (qv_le_stab_of_adj _ hμρ.symm), (isPGroup_qv _ hyp hρ).to_le hZρ,
    (ms22_iii _ hyp hb0 h.centHyp hc).2.2⟩

theorem le_relIndex_qv_zm (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    2 ^ k ≤ (Qv _ γ).relIndex (ZM _ μ) := by
  obtain ⟨-, hst, h2, hQ⟩ := zm_facts h hb4 hc
  rw [relIndex_qv_zm_eq h hb4 hc]
  exact S5B.le_relIndex_centralizer h hd hc.1 hst h2 hQ

theorem commutator_uSub_zm_le (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    ⁅S5.uSub h.le L μ, ZM _ γ⁆ ≤ ZM _ γ ⊓ ZM _ μ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨hμ, hγ, -, -, -, -, -, hσγ, -, -, hμσ, -⟩ := pair_facts h hb4 hc
  obtain ⟨-, hst, -, -⟩ := zm_facts h hb4 hc
  have hZμγ : ZM _ μ ≤ stab _ γ :=
    (zm_le_qv_of_dist_lt _ hμ (by omega)).trans (qv_le_stab_of_adj _ hσγ)
  refine le_inf ?_ ?_
  · rw [Subgroup.commutator_comm]
    refine commutator_le_left_of_le_normalizer ?_
    exact ((S5B.uSub_le_zm h.le μ).trans hZμγ).trans (stab_le_normalizer_zm _ _)
  · exact (commutator_le_left_of_le_normalizer (hst.trans (stab_le_normalizer_zm _ _))).trans'
      (Subgroup.commutator_mono (S5B.uSub_le_zm h.le μ) le_rfl)

theorem relIndex_qv_zm_le_sq (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    (Qv _ γ).relIndex (ZM _ μ) ≤ (2 ^ k) ^ 2 := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨-, hst, -, -⟩ := zm_facts h hb4 hc
  have hγ : IsMVtx _ γ := hc.isMVtx_right _ hyp
  rw [relIndex_qv_zm_eq h hb4 hc]
  refine relIndex_le_sq h hd hc.1 hst ?_
  have hab := (isElemAbelian_zm _ hyp hb0 hγ).1
  refine (commutator_uSub_zm_le h hb4 hc).trans (inf_le_left.trans ?_)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  simpa using (congrArg Subtype.val this).symm

theorem relIndex_qv_zm_symm (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ)
    (hle : (Qv _ γ).relIndex (ZM _ μ) ≤ 2 ^ k) : (Qv _ μ).relIndex (ZM _ γ) ≤ 2 ^ k := by
  obtain ⟨-, hst, h2, hQ⟩ := zm_facts h hb4 hc
  rw [relIndex_qv_zm_eq h hb4 hc] at hle
  exact relIndex_qv_le_of_relIndex_le h hd hc.1 hst h2 hQ hle

end S512T

end CFSG.Quasithin.MS93

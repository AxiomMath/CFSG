module

public import CFSG.Quasithin.MS93.S5B512O5
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.MS93.S512TThree

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512F

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_uSub_jOff_le_centralizer (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hJl : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    {δ ε : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) (hδε : (puAmalgam h.le).treeGraph.Adj δ ε) :
    ⁅S5.uSub h.le L δ, S5.jOff h.le L (2 ^ k) δ ε⁆ ≤
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) δ ε : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hδ hδε
  rw [S5B.jOff_smul h.le hLn, S5B.uSub_smul h.le hLn, ← Subgroup.map_commutator,
    PU.centralizer_map_mulEquiv]
  exact Subgroup.map_mono (S5B.commutator_uSub_le_centralizer_baseA h hd hl hJl)

theorem commutator_uSub_qv_le_xm (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hJl : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    {μ ρ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hαρ : (puAmalgam h.le).treeGraph.Adj (baseA _) ρ) (hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ)
    (hQJ : Qv _ (baseA (puAmalgam h.le)) ≤ S5.jOff h.le L (2 ^ k) μ ρ) :
    ⁅S5.uSub h.le L μ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ ≤ 2 := by
    have := dist_triangle _ (baseA (puAmalgam h.le)) ρ μ
    rw [dist_eq_one_of_adj _ hαρ, dist_eq_one_of_adj _ hρμ] at this
    exact this
  have hquad := commutator_uSub_jOff_le_centralizer h hd hl hJl hμ hρμ.symm
  have hQμ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ μ :=
    qv_le_stab_of_dist_le_two _ hyp (isMVtx_baseA _) hdμ
  have hUZ : S5.uSub h.le L μ ≤ ZM _ μ := S5B.uSub_le_zm h.le μ
  have hZQ : ZM _ μ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hμ (by rw [SimpleGraph.dist_comm]; omega)
  have hcU : ⁅S5.uSub h.le L μ, Qv _ (baseA (puAmalgam h.le))⁆ ≤ S5.uSub h.le L μ :=
    commutator_le_left_of_le_normalizer (hQμ.trans (S5B.stab_le_normalizer_uSub_at h μ))
  have hcC : ⁅S5.uSub h.le L μ, Qv _ (baseA (puAmalgam h.le))⁆ ≤
      Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) :=
    (Subgroup.commutator_mono le_rfl hQJ).trans (hquad.trans (Subgroup.centralizer_le hQJ))
  intro y hy
  refine Subgroup.subset_closure ⟨⟨hZQ (hUZ (hcU hy)), hcC hy⟩, ?_⟩
  exact (isElemAbelian_zm _ hyp hb0 hμ).2 y (hUZ (hcU hy))

omit [Fintype F] in
theorem qv_le_jOff_of_not_le (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)} (hch : S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂)
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _))
    (hc55 : S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x)
    (hμeq : μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
      μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2)
    (hL : ¬ puTrans h.le L (baseA _) ≤
      S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
        S5.zHat _ (baseA _) α') :
    Qv _ (baseA (puAmalgam h.le)) ≤
      S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨-, -, hcμ, ⟨y, hy, hμy⟩, -, hmid, hβγ⟩ := S512T.chain_geo h hb4 hch
  obtain ⟨-, -, hC⟩ := hc55
  rcases hC with halt | ⟨hQJ, -, -⟩
  · exact absurd (S512T.le_sup_of_alt1 h hb4 hch hg hx hμeq halt) hL
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hαρ : (puAmalgam h.le).treeGraph.Adj (baseA _) (y • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ y _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [hyα] at this
  have hρμ : (puAmalgam h.le).treeGraph.Adj (y • baseB (puAmalgam h.le)) μ₁ := by
    rw [hμy]
    exact (adj_smul _ y _ _).2 hβγ
  have hρ := S512T.eq_geo_one_of_adj h hb4 hcμ hmid hαρ hρμ
  rw [← hρ, hμy, S5B.jOff_smul h.le hLn]
  have hQ : Qv _ (baseA (puAmalgam h.le)) =
      (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj y).toMonoidHom := by
    rw [← qv_smul, hyα]
  rw [hQ]
  exact Subgroup.map_mono hQJ

end S512F

end CFSG.Quasithin.MS93

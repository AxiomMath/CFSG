module

public import CFSG.Quasithin.MS93.S510N1
public import CFSG.Quasithin.MS93.S510XZ

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S511

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem critR_le_xm_baseA (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) :
    critR _ (baseA (puAmalgam h.le)) α' ≤ XM _ (geo _ (baseA (puAmalgam h.le)) α' 2) := by
  have hβγ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 2)
      (baseB (puAmalgam h.le)) := by
    have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rw [hαβ] at this
    exact this.symm
  have hγM := isMVtx_geo_two _ h.hyp20 h.critDist_pos hc
  exact S510.critR_le_xm_of_le_vPre h hb hd hc hαβ hl.2.1
    ((S5B.qv_le_jOff h Nat.one_le_two_pow hγM hβγ).trans (hl.1.le.trans hl.2.2.2))

end S511

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem uSub_sup_le_zm (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ ≤ ZM _ ρ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨ε, hρε⟩ : ∃ ε, (puAmalgam h.le).treeGraph.Adj ρ ε := by
    obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
    exact ⟨g • baseB _, (adj_smul _ g _ _).2 (adj_baseA_baseB _)⟩
  refine sup_le (S5B.uSub_le_zm h.le _) ?_
  intro _ hx
  exact zh_le_zm _ hρε (S5B.stabCenter_inf_xm_le_zh h hρ hρε ⟨hx.2, hx.1⟩)

theorem critR_le_centralizer_jOff_baseA (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) :
    critR _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) : Set _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγ
  have hβγ : (puAmalgam h.le).treeGraph.Adj γ (baseB (puAmalgam h.le)) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rw [hαβ] at this
    exact this.symm
  have hγM : IsMVtx _ γ := isMVtx_geo_two _ hyp hb0 hc
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hQl : Qv _ γ ≤ S5.vPre h.le a (MSP.qLine l) :=
    (S5B.qv_le_jOff h Nat.one_le_two_pow hγM hβγ).trans (hl.1.le.trans hl.2.2.2)
  have hZγ : ZM _ α' ≤ Qv _ γ := by
    refine zm_le_qv_of_dist_lt _ hα' ?_
    rw [tdist_comm, hγ, dist_geo_right _ (by omega), hd2]
    omega
  refine (S5B.critR_le_commutator_uSub h hb hc hαβ).trans
    ((Subgroup.commutator_mono le_rfl (hZγ.trans hQl)).trans
      ((S5B.commutator_uSub_le_centralizer_baseA h hd hl.2.1 le_rfl).trans
        (Subgroup.centralizer_le ?_)))
  rw [hl.1]
  exact hl.2.2.2

end S511S

namespace S511

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem critR_not_le_stabCenter (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    ¬ critR _ γ γ' ≤ stabCenter _ γ := by
  intro hle
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hd2 : (puAmalgam h.le).treeGraph.dist γ γ' = critDist (puAmalgam h.le) := hc.2.1
  have hb2 : 2 ≤ critDist (puAmalgam h.le) := two_le_critDist _ hyp hb0
  have hγM : IsMVtx _ γ := hc.1
  have hγ'M : IsMVtx _ γ' := hc.isMVtx_right _ hyp
  have hadj : (puAmalgam h.le).treeGraph.Adj γ (geo _ γ γ' 1) := adj_geo_one _ (by omega)
  have hZ'st : ZM _ γ' ≤ stab _ γ := zm_le_stab_of_isCritical _ hyp hb0 hc
  have hU : S5.uSub h.le L γ ≤ Subgroup.centralizer (ZM _ γ' : Set (puAmalgam h.le).Universal) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hmem : z * u * z⁻¹ * u⁻¹ ∈ critR _ γ γ' := by
      have := Subgroup.commutator_mem_commutator hz (S5B.uSub_le_zm h.le _ hu)
      rw [critR, Subgroup.commutator_comm]
      rwa [commutatorElement_def] at this
    have hcL : z * u * z⁻¹ * u⁻¹ ∈
        Subgroup.centralizer (puTrans h.le L γ : Set (puAmalgam h.le).Universal) :=
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        S510.commute_of_mem_stabCenter (hle hmem) (puTrans_le_stab h.le L _ hy)
    have h1 := S510.lift_gp h hd hγM (hZ'st hz) hu hcL
    calc z * u = z * u * z⁻¹ * z := by group
      _ = u * z := by rw [h1]
  have hγ2 : IsMVtx _ (geo _ γ γ' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hadj2 : (puAmalgam h.le).treeGraph.Adj (geo _ γ γ' 1) (geo _ γ γ' 2) :=
    adj_geo _ (i := 1) (by omega)
  have hZH : ZH _ (geo _ γ γ' 1) ≤
      Subgroup.centralizer (ZM _ γ' : Set (puAmalgam h.le).Universal) := by
    have h1 : ZM _ γ' ≤ Qv _ (geo _ γ γ' 2) := by
      refine zm_le_qv_of_dist_lt _ hγ'M ?_
      rw [tdist_comm, dist_geo_right _ (by omega), hd2]
      omega
    have h2 : ZH _ (geo _ γ γ' 1) ≤ XM _ (geo _ γ γ' 2) :=
      (zh_le_zm _ hadj2.symm).trans (zm_le_xm _ hyp hb0 hγ2)
    rw [Subgroup.le_centralizer_iff]
    exact h1.trans ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le h2))
  apply ms22_ii _ hyp hb0 hC hc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, S5B.zm_eq_zh_sup_uSub h hγM hadj]
  exact sup_le hZH hU

theorem le_relIndex_zm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    2 ^ k ≤ (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hcr' := ms22_iii _ hyp hb0 h.centHyp hc
  have hd' : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) := hcr'.2.1
  have hadj : (puAmalgam h.le).treeGraph.Adj α' (geo _ α' (baseA (puAmalgam h.le)) 1) :=
    adj_geo_one _ (by omega)
  have hZ2 : IsPGroup 2 (ZM _ α') :=
    (isPGroup_qv _ hyp ((isMVtx_iff_of_adj _ hadj).1 hα')).to_le
      ((zm_le_qv_self _ hα' hb0).trans (qv_le_qv _ hyp hα' hadj))
  have h1 := S5B.le_relIndex_centralizer h hd hα (zm_le_stab_of_isCritical _ hyp hb0 hc) hZ2
    hcr'.2.2
  have hQC : Qv _ α' ≤ Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal) :=
    (qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le (zm_le_xm _ hyp hb0 hα'))
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have : Finite ↥(Qv _ (baseB (puAmalgam h.le))) :=
    finite_qv _ hyp ((isMVtx_iff_of_adj _ hαβ).1 hα)
  have : Finite ↥(ZM _ (baseA (puAmalgam h.le))) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ hyp hα hαβ)))
  calc 2 ^ k ≤ (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L (baseA _)) := h1
    _ ≤ (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
        (ZM _ (baseA (puAmalgam h.le))) :=
      Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le _) Subgroup.FiniteIndex.index_ne_zero
    _ ≤ (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) :=
      Subgroup.relIndex_le_of_le_left hQC Subgroup.FiniteIndex.index_ne_zero

namespace IsChain

variable {h : PUHyp M T L} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

omit [Fintype F] in
theorem cent_at {Good : Vtx (puAmalgam h.le) → Vtx (puAmalgam h.le) → Prop}
    (hch : S510.IsChain h (2 ^ k) a s t N)
    (hcent : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ → ∀ μ, Good α' μ →
        ¬ ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) →
        ZM _ μ ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
          stabCenter _ (baseA (puAmalgam h.le)))
    {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N)
    (hgood : ∃ g : (puAmalgam h.le).Universal, geo _ s t (2 * j) = g • baseA (puAmalgam h.le) ∧
      geo _ s t (2 * j + 1) = g • baseB _ ∧
      Good (g⁻¹ • geo _ s t (2 * j + critDist (puAmalgam h.le))) (g⁻¹ • geo _ s t (2 * j - 2))) :
    ZM _ (geo _ s t (2 * j - 2)) ⊓ ZM _ (geo _ s t (2 * j)) ⊓ ZM _ (geo _ s t (2 * j + 2)) ≤
      stabCenter _ (geo _ s t (2 * j)) := by
  have hdd := hch.dist_eq
  have hb2 : 2 ≤ critDist (puAmalgam h.le) := two_le_critDist _ h.hyp20 h.critDist_pos
  obtain ⟨g, hg0, hg1, hgd⟩ := hgood
  have hcr := hch.crit j hjN
  have hcr0 := hch.crit (j - 1) (by omega)
  rw [show 2 * (j - 1) = 2 * j - 2 by omega] at hcr0
  have hg2 := hch.geo_eq (i := 2 * j) (j := 2 * j + critDist (puAmalgam h.le)) (m := 2)
    (by omega) (by omega) (by omega)
  have hg1' := hch.geo_eq (i := 2 * j) (j := 2 * j + critDist (puAmalgam h.le)) (m := 1)
    (by omega) (by omega) (by omega)
  have hg2' := hch.geo_eq' (i := 2 * j) (j := 2 * j + critDist (puAmalgam h.le)) (m := 2)
    (by omega) (by omega) (by omega)
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have e0 : baseA (puAmalgam h.le) = g⁻¹ • P (2 * j) := by rw [hg0, inv_smul_smul]
  have hc' : IsCritical _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * j + b)) := by
    have := (isCritical_smul _ g⁻¹ _ _).2 hcr
    rwa [← e0] at this
  have hgeo : ∀ i, geo _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * j + b)) i =
      g⁻¹ • geo _ (P (2 * j)) (P (2 * j + b)) i := by
    intro i
    rw [e0, geo_smul]
  have hβ' : geo _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * j + b)) 1 = baseB _ := by
    rw [hgeo, hg1', hg1, inv_smul_smul]
  have hδ : geo _ (baseA (puAmalgam h.le)) (g⁻¹ • P (2 * j + b)) 2 = g⁻¹ • P (2 * j + 2) := by
    rw [hgeo, hg2]
  have hδ' : geo _ (g⁻¹ • P (2 * j + b)) (baseA (puAmalgam h.le)) 2 =
      g⁻¹ • P (2 * j - 2 + b) := by
    rw [e0, geo_smul, hg2', show 2 * j + b - 2 = 2 * j - 2 + b by omega]
  have hZμ : ¬ ZM _ (g⁻¹ • P (2 * j - 2)) ≤
      Qv _ (geo _ (g⁻¹ • P (2 * j + b)) (baseA (puAmalgam h.le)) 2) := by
    rw [hδ', zm_smul, qv_smul, map_conj_le_map_conj_iff]
    exact hcr0.2.2
  have key := hcent _ hc' hβ' _ hgd hZμ
  rw [hδ] at key
  have e1 : P (2 * j - 2) = g • (g⁻¹ • P (2 * j - 2)) := (smul_inv_smul g _).symm
  have e2 : P (2 * j + 2) = g • (g⁻¹ • P (2 * j + 2)) := (smul_inv_smul g _).symm
  rw [e1, e2, hg0, zm_smul (g := g), zm_smul (g := g), zm_smul (g := g), S510.stabCenter_smul,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_conj_le_map_conj_iff]
  exact key

end IsChain

end S511

end CFSG.Quasithin.MS93

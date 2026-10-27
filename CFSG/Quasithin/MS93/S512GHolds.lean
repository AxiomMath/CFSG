module

public import CFSG.Quasithin.MS93.S512GFrame
public import CFSG.Quasithin.MS93.S512FAlt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512G

theorem relIndex_comm_of_card_eq {Γ : Type*} [Group Γ] {H K : Subgroup Γ} (hK : Nat.card K ≠ 0)
    (hc : Nat.card H = Nat.card K) : H.relIndex K = K.relIndex H := by
  have h1 := Subgroup.relIndex_mul_card H K
  have h2 := Subgroup.relIndex_mul_card K H
  rw [inf_comm, hc] at h2
  have h0 : Nat.card ↥(H ⊓ K) ≠ 0 := fun h0 => hK (by rw [← h1, h0, mul_zero])
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero h0) (h1.trans h2.symm)

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem relIndex_qv_comm (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex (Qv _ γ) =
      (Qv _ γ).relIndex (Qv _ (baseA (puAmalgam h.le))) := by
  have : Finite ↥(stab (puAmalgam h.le) γ) := S310.finite_stab_of_isMVtx h hγ
  have : Finite ↥(Qv (puAmalgam h.le) γ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab _ γ))
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hγ
  refine relIndex_comm_of_card_eq Nat.card_pos.ne' ?_
  rw [qv_smul, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]

theorem twoAlt2_holds (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h55 : S55)
    (h56 : S56) (hq2 : S5B.Q2Cent) : S512T.TwoAlt2 := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' _ μ₁ μ₂ hch hbad hQ _ hline _ g hg x hx hc55
    hμeq hL
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hq1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have h58 := S5B.s58_of h32 hX2 h52 h54 h55 h56
  obtain ⟨hc, hαβ, hcμ, ⟨y, hy, hμy⟩, -, hmid, hβγ⟩ := S512T.chain_geo h hb4 hch
  have hμ₁ := hch.2.2.2.2.1
  obtain ⟨-, ⟨c, hc1, hc2, hc3⟩, hcμ₂⟩ := hch.2.2.2.2.2.2
  rw [hmid] at hc3 hcμ₂
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    (isMVtx_iff_of_adj _ hβγ.symm).2 (not_isMVtx_baseB _)
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hαρ : (puAmalgam h.le).treeGraph.Adj (baseA _) (y • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ y _ _).2 (adj_baseA_baseB (puAmalgam h.le))
    rwa [hyα] at this
  have hρμ : (puAmalgam h.le).treeGraph.Adj (y • baseB (puAmalgam h.le)) μ₁ := by
    rw [hμy]
    exact (adj_smul _ y _ _).2 hβγ
  have hρ := S512T.eq_geo_one_of_adj h hb4 hcμ hmid hαρ hρμ
  have hgf : geo _ (baseA (puAmalgam h.le)) (c • geo _ (baseA (puAmalgam h.le)) α' 2) 2 =
      c • baseA (puAmalgam h.le) := by
    have e := geo_smul _ c μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 2
    rwa [hc1, hmid] at e
  refine false_of_frame (k := k) (α' := c • geo _ (baseA (puAmalgam h.le)) α' 2) (μ := c • μ₂)
    (δ' := c • α') h14 hSQ hT h32 hX2 h52 h54 h55 h56 hq2 h hmin hb4 hd ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hline ?_ ?_ ?_
  · have e := (isCritical_smul _ c μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2)).2 hcμ
    rwa [hc1] at e
  · have e := geo_smul _ c μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1
    rwa [hc1, hc2] at e
  · have e := S5B.relIndex_qv_zm_smul c (geo _ (baseA (puAmalgam h.le)) α' 2) μ₁
    rw [hc1] at e
    rw [e]
    exact hbad
  · rw [hgf]
    exact hc3
  · rw [hgf]
    exact (isCritical_smul _ c _ _).2 hcμ₂
  ·
    rw [hgf]
    intro hJJ
    obtain ⟨-, -, hC⟩ := hc55
    rcases hC with halt | ⟨-, hidx, -⟩
    · exact hL (S512T.le_sup_of_alt1 h hb4 hch hg hx hμeq halt)
    have e1 : S5.jOff h.le L (2 ^ k) (c • baseA (puAmalgam h.le)) (baseB _) =
        (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)).map (MulAut.conj (c * y)).toMonoidHom := by
      rw [← S5B.jOff_smul h.le hLn, mul_smul, mul_smul, hyα, hρ, hc2]
    have e2 : S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) =
        (S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _)).map
          (MulAut.conj (c * y)).toMonoidHom := by
      rw [← S5B.jOff_smul h.le hLn, mul_smul, mul_smul, ← hμy, hc1, hρ, hc2]
    have hJ : S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) =
        S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) :=
      Subgroup.map_injective (f := (MulAut.conj (c * y)).toMonoidHom)
        (MulAut.conj (c * y)).injective (e1.symm.trans (hJJ.trans e2))
    have hQγ := S5B.qv_le_jOff h hq1 hγM hβγ.symm
    have hle : Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
        S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) ⊓
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) :=
      le_inf hQγ (hQγ.trans hJ.symm.le)
    have hfin : Finite ↥(Qv (puAmalgam h.le) (baseB _)) := finite_qv _ hyp (not_isMVtx_baseB _)
    have hJfin : Finite ↥(S5.jOff h.le L (2 ^ k) (geo _ (baseA (puAmalgam h.le)) α' 2)
        (baseB _) ⊓ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) :=
      Finite.of_injective _ (Subgroup.inclusion_injective
        (inf_le_left.trans (S5B.jOff_le_qv h.le L _ _ _)))
    have h1 := Subgroup.relIndex_le_of_le_right (H := Qv _ (baseA (puAmalgam h.le))) hle
      (by exact Subgroup.index_ne_zero_of_finite)
    have hQ' : (2 ^ k) ^ 2 < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex
        (Qv _ (baseA (puAmalgam h.le))) := by
      have e : (Qv _ (y • geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex
          (Qv _ (y • baseA (puAmalgam h.le))) =
          (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex
            (Qv _ (baseA (puAmalgam h.le))) := by
        rw [qv_smul, qv_smul,
          Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj y).injective]
      rw [← hμy, hyα] at e
      rw [← e]
      exact hQ
    have hs := relIndex_qv_comm h hγM
    omega
  · rw [hgf]
    have e : (Qv _ (c • μ₁)).relIndex (Qv _ (c • baseA (puAmalgam h.le))) =
        (Qv _ μ₁).relIndex (Qv _ (baseA (puAmalgam h.le))) := by
      rw [qv_smul, qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj c).injective]
    rw [hc1] at e
    rw [e]
    exact hQ
  · rw [hgf]
    have e := Subgroup.map_mono (f := (MulAut.conj c).toMonoidHom)
      (S512F.qv_le_jOff_of_not_le h hb4 hch hg hx hc55 hμeq hL)
    rwa [← qv_smul, ← S5B.jOff_smul h.le hLn, hc1, hc2] at e
  · rw [hgf]
    exact (isCritical_smul _ c _ _).2 hc
  · rw [hgf, geo_smul]
  · rw [hgf]
    have hμ₁e : c⁻¹ • baseA (puAmalgam h.le) = μ₁ := by rw [← hc1, inv_smul_smul]
    refine ⟨c⁻¹, inv_smul_smul c _, ?_, ?_⟩
    · rw [geo_smul, inv_smul_smul, hαβ]
    · rw [inv_smul_smul, hμ₁e]
      exact ⟨_, hβγ, S5B.not_uSub_le_bSub_of_isCritical h58 h hmin hb hd hc, hμ₁⟩

end S512G

end CFSG.Quasithin.MS93

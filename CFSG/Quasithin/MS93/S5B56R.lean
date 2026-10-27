module

public import CFSG.Quasithin.MS93.S5BAux

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S5C56

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_zm_le_centralizer_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {K : Subgroup (puAmalgam h.le).Universal}
    (hKβ : K ≤ Qv _ (baseB (puAmalgam h.le))) (hKl : K ≤ S5.vPre h.le a (MSP.qLine l)) :
    ⁅ZM _ (baseA (puAmalgam h.le)), K⁆ ≤ Subgroup.centralizer (K : Set _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hUT : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ Qv _ (baseB (puAmalgam h.le)) :=
    (commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans
      (stab_le_normalizer_zm _ _))).trans ((zm_le_qv_self _ hα hb0).trans (qv_le_qv _ hyp hα hαβ))
  have hn : ZH _ (baseB (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.uSub h.le L (baseA (puAmalgam h.le)) : Set _) :=
    ((zh_le_qv _ _).trans (qv_le_stab_of_adj _ hαβ.symm)).trans
      (le_normalizer_commutator (stab_le_normalizer_zm _ _)
        (stab_le_normalizer_puTrans h.le hLn _))
  have hZK : ⁅ZM _ (baseA (puAmalgam h.le)), K⁆ ≤
      ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), K⁆ := by
    rw [Subgroup.commutator_le]
    intro z hz j hj
    rw [S5B.zm_eq_zh_sup_uSub h hα hαβ] at hz
    have hz' : z ∈ ((ZH _ (baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) *
        (S5.uSub h.le L (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn]
      exact hz
    obtain ⟨z₀, hz₀, u, hu, rfl⟩ := hz'
    have h1 : z₀ * (u * j * u⁻¹) = (u * j * u⁻¹) * z₀ :=
      (Subgroup.mem_centralizer_iff.1 (zh_le_centralizer _ _ hz₀) _
        (mul_mem (mul_mem (hUT hu) (hKβ hj)) (inv_mem (hUT hu)))).symm
    have e : ⁅z₀ * u, j⁆ = ⁅u, j⁆ := by
      simp only [commutatorElement_def]
      calc z₀ * u * j * (z₀ * u)⁻¹ * j⁻¹ = z₀ * (u * j * u⁻¹) * z₀⁻¹ * j⁻¹ := by group
        _ = u * j * u⁻¹ * j⁻¹ := by rw [h1]; group
    rw [e]
    exact Subgroup.commutator_mem_commutator hu hj
  exact hZK.trans (S5B.commutator_uSub_le_centralizer_baseA h hd hl hKl)

theorem commutator_zm_qv_le_centralizer_jOff (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hJl : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hJδ : S5.jOff h.le L (2 ^ k) δ (baseB _) = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) :
    ⁅ZM _ δ, Qv _ (baseA (puAmalgam h.le))⁆ ≤
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set _) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨t, ht, htα⟩ := exists_mem_stab_smul _ hαβ.symm hβδ
  have htβ : t • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 ht
  have htβ' : t⁻¹ • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 (inv_mem ht)
  have htJ : (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) := by
    have e := S5B.jOff_smul h.le hLn (2 ^ k) t (baseA (puAmalgam h.le)) (baseB _)
    rw [htα, htβ, hJδ] at e
    exact e.symm
  have htJ' : (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t⁻¹).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) := by
    calc _ = ((S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
          (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom := by rw [htJ]
      _ = _ := map_conj_inv_map_conj _ t
  have hQ : Qv _ (t⁻¹ • baseA (puAmalgam h.le)) ≤
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) := by
    have hadj : (puAmalgam h.le).treeGraph.Adj (t⁻¹ • baseA (puAmalgam h.le)) (baseB _) := by
      have := (adj_smul _ t⁻¹ _ _).2 hαβ
      rwa [htβ'] at this
    have hM : IsMVtx _ (t⁻¹ • baseA (puAmalgam h.le)) := (isMVtx_smul _ _ _).2 hα
    have e := S5B.jOff_smul h.le hLn (2 ^ k) t⁻¹ (baseA (puAmalgam h.le)) (baseB _)
    rw [htJ', htβ'] at e
    exact (S5B.qv_le_jOff h Nat.one_le_two_pow hM hadj).trans e.le
  have hZ : ZM _ δ = (ZM _ (baseA (puAmalgam h.le))).map (MulAut.conj t).toMonoidHom := by
    rw [← htα, zm_smul]
  have hQα : Qv _ (baseA (puAmalgam h.le)) =
      (Qv _ (t⁻¹ • baseA (puAmalgam h.le))).map (MulAut.conj t).toMonoidHom := by
    rw [← qv_smul, smul_inv_smul]
  have h1 : ⁅ZM _ (baseA (puAmalgam h.le)), Qv _ (t⁻¹ • baseA (puAmalgam h.le))⁆ ≤
      Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) :=
    (Subgroup.commutator_mono le_rfl hQ).trans
      (commutator_zm_le_centralizer_baseA h hd hl (S5B.jOff_le_qv h.le L _ _ _) hJl)
  rw [hZ, hQα, ← Subgroup.map_commutator]
  calc _ ≤ (Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _)).map
          (MulAut.conj t).toMonoidHom :=
        Subgroup.map_mono h1
    _ = _ := by rw [← PU.centralizer_map_mulEquiv, htJ]

end S5C56

end CFSG.Quasithin.MS93

module

public import CFSG.Quasithin.MS93.S310A

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S5NQ

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem commutator_mem_dSub_baseA (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {δ : Vtx (puAmalgam h.le)} (hδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2)
    {x : (puAmalgam h.le).Universal} (hxZ : x ∈ ZM _ δ) (hxB : x ∈ S5.bSub h.le L (baseA _))
    {q : (puAmalgam h.le).Universal} (hq : q ∈ Qv _ (baseA (puAmalgam h.le))) :
    ⁅x, q⁆ ∈ S5.dSub h.le L (baseA _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hδM : IsMVtx _ δ := ((even_dist_iff _ _ δ).1 (by rw [hδ]; exact even_two)).1 hα
  have hαε : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) δ 1) :=
    adj_geo_one _ (by omega)
  have hεδ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) δ 1) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := δ) (i := 1) (by omega)
    rwa [show (1 + 1 : ℕ) = 2 from rfl, ← hδ, geo_dist] at this
  have hε : ¬ IsMVtx _ (geo _ (baseA (puAmalgam h.le)) δ 1) := (isMVtx_iff_of_adj _ hαε).1 hα
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hZδQ : ZM _ δ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hδM (by rw [SimpleGraph.dist_comm, hδ]; omega)
  have hQδn : Qv _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (ZM _ δ : Set (puAmalgam h.le).Universal) :=
    (qv_le_stab_of_dist_le_two _ hyp hα hδ.le).trans (stab_le_normalizer_zm _ _)
  have hxQ : x ∈ Qv _ (baseA (puAmalgam h.le)) := hZδQ hxZ
  have hQα : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ (baseA _) := qv_le_stab _ _
  have hLA : puTrans h.le L (baseA _) ≤ stab _ (baseA (puAmalgam h.le)) :=
    puTrans_le_stab h.le L _
  have hcQ : ⁅x, q⁆ ∈ Qv _ (baseA (puAmalgam h.le)) := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hxQ hq) (inv_mem hxQ)) (inv_mem hq)
  set S : Set (puAmalgam h.le).Universal := {g | ∃ q ∈ Qv _ (baseA (puAmalgam h.le)), ⁅x, q⁆ = g}
    with hS
  set Y := Subgroup.closure S with hY
  have hcY : ⁅x, q⁆ ∈ Y := Subgroup.subset_closure ⟨q, hq, rfl⟩
  have hYZ : Y ≤ ZM _ δ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨q', hq', rfl⟩
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    refine mul_mem hxZ ?_
    rw [← mul_assoc]
    exact (Subgroup.mem_normalizer_iff.1 (hQδn hq') _).1 (inv_mem hxZ)
  have hconj : ∀ l ∈ puTrans h.le L (baseA _), ∀ q' ∈ Qv _ (baseA (puAmalgam h.le)),
      l * ⁅x, q'⁆ * l⁻¹ = ⁅x, l * q' * l⁻¹⁆ := by
    intro l hl q' hq'
    have hw : ⁅l, x⁆ ∈ ZM _ (baseA (puAmalgam h.le)) := by
      rw [← commutatorElement_inv]
      exact inv_mem (S310.commutator_mem_zm_of_mem_bSub h hb hxB hl)
    have hq'' : l * q' * l⁻¹ ∈ Qv _ (baseA (puAmalgam h.le)) :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_qv _ _ (hLA hl)) _).1 hq'
    have hxq : x * (l * q' * l⁻¹) * x⁻¹ ∈ Qv _ (baseA (puAmalgam h.le)) :=
      mul_mem (mul_mem hxQ hq'') (inv_mem hxQ)
    have hcomm : ⁅l, x⁆ * (x * (l * q' * l⁻¹) * x⁻¹) = (x * (l * q' * l⁻¹) * x⁻¹) * ⁅l, x⁆ :=
      ((Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα hw)) _ hxq).symm
    calc l * ⁅x, q'⁆ * l⁻¹ = ⁅l, x⁆ * (x * (l * q' * l⁻¹) * x⁻¹) * ⁅l, x⁆⁻¹ *
          (l * q' * l⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅x, l * q' * l⁻¹⁆ := by
          rw [hcomm, mul_inv_cancel_right]
          simp only [commutatorElement_def]
  have hYn : puTrans h.le L (baseA _) ≤
      Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun l hl => ?_
    rw [hY, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨_, ⟨q', hq', rfl⟩, rfl⟩
    refine ⟨l * q' * l⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_qv _ _ (hLA hl)) _).1 hq'
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hconj l hl q' hq']
  by_cases hQ : Qv _ δ ≤ Qv _ (baseA (puAmalgam h.le))
  · have : Finite ↥(Qv _ (baseA (puAmalgam h.le))) := by
      rw [S5B.qv_baseA_eq h]
      exact S5B.finite_imM h.le _
    have hQe : Qv _ δ = Qv _ (baseA (puAmalgam h.le)) :=
      Subgroup.eq_of_le_of_card_ge hQ (S5B.card_qv_eq h hδM).symm.le
    have h1 : ⁅x, q⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact ((Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hδM hxZ)) q
        (hQe ▸ hq)).symm
    rw [h1]
    exact one_mem _
  · obtain ⟨y, hyδ, hyα⟩ := Set.not_subset.1 hQ
    have hyε : y ∈ Qv _ (geo _ (baseA (puAmalgam h.le)) δ 1) := qv_le_qv _ hyp hδM hεδ.symm hyδ
    have hyst : y ∈ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_isMVtx _ hyp hα hαε hyε
    have hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1 := by
      obtain ⟨e, he⟩ := isPGroup_qv _ hyp hε ⟨y, hyε⟩
      exact ⟨e, by simpa using congrArg Subtype.val he⟩
    have hbot : Subgroup.normalizer ((⊥ : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal) = ⊤ := Subgroup.normalizer_eq_top _
    have hyW : ∀ w ∈ Y, y * w * y⁻¹ * w⁻¹ ∈ (⊥ : Subgroup (puAmalgam h.le).Universal) := by
      intro w hw
      have hwc := (Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hδM (hYZ hw))) y hyδ
      rw [Subgroup.mem_bot, hwc, mul_inv_cancel_right, mul_inv_cancel]
    have hcore := S310.commutator_le_of_two_elt_baseA h (W := Y) (Z := ⊥)
      ((hYZ.trans hZδQ).trans hQα) bot_le hYn (by rw [hbot]; exact le_top) hyst hy2 hyα
      (by rw [hbot]; exact Subgroup.mem_top _) hyW
    have hYC : Y ≤
        Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 hcore)
    exact ⟨hcQ, hYC hcY⟩

theorem commutator_mem_dSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {γ δ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ) (hδ : (puAmalgam h.le).treeGraph.dist γ δ = 2)
    {x : (puAmalgam h.le).Universal} (hxZ : x ∈ ZM _ δ) (hxB : x ∈ S5.bSub h.le L γ)
    {q : (puAmalgam h.le).Universal} (hq : q ∈ Qv _ γ) : ⁅x, q⁆ ∈ S5.dSub h.le L γ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hγ
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hδ' : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • δ) = 2 := by
    rw [← dist_smul _ g, smul_inv_smul]
    exact hδ
  have hxZ' : g⁻¹ * x * g ∈ ZM _ (g⁻¹ • δ) := by
    have e : ZM (puAmalgam h.le) δ = (ZM _ (g⁻¹ • δ)).map (MulAut.conj g).toMonoidHom := by
      rw [← zm_smul, smul_inv_smul]
    rw [e, mem_map_conj] at hxZ
    exact hxZ
  have hxB' : g⁻¹ * x * g ∈ S5.bSub h.le L (baseA _) := by
    rw [S5B.bSub_smul h.le hLn, mem_map_conj] at hxB
    exact hxB
  have hq' : g⁻¹ * q * g ∈ Qv _ (baseA (puAmalgam h.le)) := by
    rw [qv_smul, mem_map_conj] at hq
    exact hq
  have key := commutator_mem_dSub_baseA h hb hδ' hxZ' hxB' hq'
  rw [S5B.dSub_smul h.le hLn, mem_map_conj]
  have e : g⁻¹ * ⁅x, q⁆ * g = ⁅g⁻¹ * x * g, g⁻¹ * q * g⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact key

end S5NQ

end CFSG.Quasithin.MS93

module

public import CFSG.Quasithin.MS93.S5A55Lift
public import CFSG.Quasithin.MS93.S5A56Hat
public import CFSG.Quasithin.MS93.S33SpS5

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix

namespace S5

section Sp

variable {F : Type} [Field F]

theorem mem_of_transv_mem_qPoint {p : Submodule F (MSP.V4 F)} {v : MSP.V4 F} {c : F} (hc : c ≠ 0)
    (ht : MSP.transv v c ∈ MSP.qPoint p) : v ∈ p := by
  by_cases hex : ∃ x ∈ MSP.perp p, MSP.form F v x ≠ 0
  · obtain ⟨x, hx, hne⟩ := hex
    have h1 := (MSP.mem_qPoint.1 ht).2 x hx
    rw [MSP.transv_mulVec, add_sub_cancel_left] at h1
    have h2 := p.smul_mem (c * MSP.form F v x)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hne), one_smul] at h2
  · push Not at hex
    rw [← MSP.perp_perp p, MSP.mem_perp]
    intro w hw
    rw [MSP.form_swap, hex w hw, neg_zero]

theorem qPoint_sup_eq_top_of_transv_mem [CharP F 2] {w v : MSP.V4 F} (hw : w ≠ 0) {c : F}
    (hc : c ≠ 0) (hvw : MSP.form F v w ≠ 0) {K : Subgroup (MSP.Sp4 F)}
    (hK : MSP.transv v c ∈ K) :
    MSP.qPoint (F ∙ w) ⊔ K = ⊤ := by
  set t := MSP.transv v c with ht
  have htw : MSP.mat t *ᵥ w = w + (c * MSP.form F v w) • v := MSP.transv_mulVec v c w
  have htw0 : MSP.mat t *ᵥ w ≠ 0 := fun h0 =>
    hw (MSP.mulVec_mat_injective t (show MSP.mat t *ᵥ w = MSP.mat t *ᵥ 0 by
      rw [h0, Matrix.mulVec_zero]))
  have hopp : ¬ (F ∙ (MSP.mat t *ᵥ w)) ≤ MSP.perp (F ∙ w) := by
    intro hle
    have h1 := MSP.mem_perp_span.1 (hle (Submodule.mem_span_singleton_self _))
    rw [htw, map_add, map_smul, MSP.form_self, zero_add, smul_eq_mul, MSP.form_swap v w] at h1
    have h2 : c * MSP.form F v w * MSP.form F v w = 0 := by
      have := congrArg Neg.neg h1
      rwa [neg_zero, ← mul_neg, neg_neg] at this
    exact mul_ne_zero (mul_ne_zero hc hvw) hvw h2
  have htop := MSP.qPoint_sup_qPoint_eq_top (MSP.isPoint_span hw) (MSP.isPoint_span htw0) hopp
  have hmap : MSP.qPoint (F ∙ (MSP.mat t *ᵥ w)) =
      (MSP.qPoint (F ∙ w)).map (MulAut.conj t).toMonoidHom := by
    rw [MSP.qPoint_map_conj, Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply]
  refine eq_top_iff.2 (htop ▸ sup_le le_sup_left ?_)
  rw [hmap]
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem (mul_mem (Subgroup.mem_sup_right hK) (Subgroup.mem_sup_left hy))
    (inv_mem (Subgroup.mem_sup_right hK))

end Sp

section PointCase

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)} (h : PUHyp M T L)

theorem exists_transv_mem_zHat_of_qPoint (hd : IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') (hβ : geo _ (baseA _) α' 1 = baseB _)
    {v : MSP.V4 F} (hv : v ≠ 0) (hT : imSp a T = MSP.qPoint (F ∙ v)) :
    ∃ c : F, c ≠ 0 ∧ MSP.transv v c ∈ vIm h.le a (zHat _ (baseA (puAmalgam h.le)) α') := by
  have := hd.charP
  have hb0 := h.critDist_pos
  have hZst : ZM (puAmalgam h.le) α' ≤ stab (puAmalgam h.le) (baseA _) :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  have hZ2 : IsPGroup 2 (ZM (puAmalgam h.le) α') :=
    (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le (zm_le_qv_baseB h hc hβ)
  have hZT : vIm h.le a (ZM _ α') ≤ MSP.qPoint (F ∙ v) := by
    have := vIm_mono' (a := a) h (zm_le_qv_baseB h hc hβ)
    rwa [puAmalgam.qv_baseB, vIm_imM h, hT] at this
  have hcen : ∀ {v' : MSP.V4 F}, v' ≠ 0 → MSP.transv v' 1 ∈ vIm h.le a (ZM _ α') →
      ∃ l : F, l ≠ 0 ∧ v' = l • v := by
    intro v' hv' h1
    obtain ⟨l, hl⟩ := Submodule.mem_span_singleton.1 (mem_of_transv_mem_qPoint one_ne_zero (hZT h1))
    refine ⟨l, fun hl0 => hv' ?_, hl.symm⟩
    rw [← hl, hl0, zero_smul]
  rcases S33.shape_of_sp4Data h hd hc with ⟨-, hzh, p', hp', hZp⟩ | ⟨-, hrel2, hfin⟩
  ·
    obtain ⟨v', hv', rfl⟩ := MSP.exists_eq_span_of_isPoint hp'
    have h1 : MSP.transv v' 1 ∈ vIm h.le a (ZM _ α') := hZp ▸ MSP.transv_mem_xPoint v' 1
    obtain ⟨l, hl0, rfl⟩ := hcen hv' h1
    refine ⟨l ^ 2 * 1, mul_ne_zero (pow_ne_zero 2 hl0) one_ne_zero, ?_⟩
    rw [hzh, ← MSP.transv_smul_vec]
    exact h1
  · by_cases hhat : ∃ t₁ t₂ t₃, IsHatTriple _ (baseA (puAmalgam h.le)) α' t₁ t₂ t₃ ∧
        t₃ ∉ Subgroup.closure ({t₁, t₂} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α'
    ·
      exfalso
      obtain ⟨t₁, t₂, t₃, ht, hn⟩ := hhat
      obtain ⟨hk1, -, -, -⟩ := S33.of_isHatTriple h hd hc ht
      have hq : Nat.card F = 2 := by rw [hd.nat_card_eq, hk1]; rfl
      have hZh := zHat_eq_of_isHatTriple h hd hq hc ht hn
      have hZ4 : 4 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') := by
        rw [hk1] at hrel2
        exact hrel2
      obtain ⟨v₁, v₂, h₁, h₂, h₁₂, -, hZv₁, hZv₂, -⟩ := hat_shape h hd hq hc ht hZh hZ4
      obtain ⟨l₁, hl₁, rfl⟩ := hcen h₁ hZv₁
      obtain ⟨l₂, hl₂, rfl⟩ := hcen h₂ hZv₂
      have e1 : l₁ = 1 := (eq_zero_or_eq_one_of_card_two hq l₁).resolve_left hl₁
      have e2 : l₂ = 1 := (eq_zero_or_eq_one_of_card_two hq l₂).resolve_left hl₂
      exact h₁₂ (by rw [e1, e2])
    ·
      have hzh := zHat_eq_of_not hhat
      have hZq := commSp_le_fixSp_zm h hd hc
      have hf2 : Module.finrank F (MSP.fixSp (vIm h.le a (ZM _ α'))) = 2 :=
        le_antisymm hfin (two_le_finrank_fixSp hZq)
      have hZ2' : IsPGroup 2 (vIm h.le a (ZM _ α')) := by
        rintro ⟨_, m, hm, rfl⟩
        obtain ⟨n, hn⟩ := hZ2 ⟨_, hm⟩
        refine ⟨n, Subtype.ext ?_⟩
        have h1 : (puAmalgam h.le).ofA (m ^ 2 ^ n) = (puAmalgam h.le).ofA 1 := by
          rw [map_pow, map_one]
          simpa using congrArg Subtype.val hn
        rw [Subgroup.coe_pow, ← map_pow, (puAmalgam h.le).ofA_injective h1, map_one]
        rfl
      obtain ⟨hm, hZm⟩ := MSP.isLine_fixSp_of_finrank_two hZ2' hf2
      have hpm : (F ∙ v) ≤ MSP.fixSp (vIm h.le a (ZM _ α')) := by
        have := MSP.fixSp_antitone hZT
        rwa [MSP.fixSp_qPoint (MSP.isPoint_span hv)] at this
      have hcard : Nat.card F ^ 2 ≤ Nat.card ↥(vIm h.le a (ZM _ α')) := by
        rw [card_vIm h hd hZst hZ2, hd.nat_card_eq]
        exact hrel2
      have heq : vIm h.le a (ZM _ α') = MSP.qLine (MSP.fixSp (vIm h.le a (ZM _ α'))) ⊓
          MSP.qPoint (F ∙ v) := Subgroup.eq_of_le_of_card_ge (le_inf hZm hZT)
        (by rw [card_qLine_inf_qPoint (MSP.isPoint_span hv) hm hpm]; exact hcard)
      refine ⟨1, one_ne_zero, ?_⟩
      rw [hzh, heq]
      exact ⟨MSP.xPoint_le_qLine hm hpm (MSP.transv_mem_xPoint v 1),
        MSP.xPoint_le_qPoint (MSP.isPoint_span hv) (MSP.transv_mem_xPoint v 1)⟩

theorem concl55_of_point (hd : IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') (hβ : geo _ (baseA _) α' 1 = baseB _)
    {δ : Vtx (puAmalgam h.le)} (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ)
    (hJ : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) = Qv _ (baseB _))
    {v : MSP.V4 F} (hv : v ≠ 0) (hT : imSp a T = MSP.qPoint (F ∙ v)) :
    ∃ g ∈ stab _ (baseA (puAmalgam h.le)), ∃ x ∈ puTrans h.le L (baseA _),
      Concl55 h (2 ^ k) α' δ g x := by
  have := hd.charP
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨c, hc0, htZ⟩ := exists_transv_mem_zHat_of_qPoint h hd hc hβ hv hT
  obtain ⟨u, hu⟩ := MSP.exists_form_eq_one hv
  set s := MSP.transv u 1 with hs
  set w := MSP.mat s *ᵥ v with hw
  have hvw : MSP.form F v w ≠ 0 := by
    rw [hw, hs, MSP.transv_mulVec, map_add, map_smul, MSP.form_self, zero_add, smul_eq_mul,
      one_mul, MSP.form_swap v u, hu, mul_one]
    exact neg_ne_zero.2 one_ne_zero
  have hw0 : w ≠ 0 := fun h0 => hvw (by rw [h0, map_zero])
  have hopp : ¬ (F ∙ w) ≤ MSP.perp (F ∙ v) := fun hle =>
    hvw (MSP.mem_perp_span.1 (hle (Submodule.mem_span_singleton_self w)))
  obtain ⟨m₀, hm₀⟩ := hd.surj s⁻¹
  set g := (puAmalgam h.le).ofA m₀ with hg
  have hgst : g ∈ stab _ (baseA (puAmalgam h.le)) := ofA_range_eq h.le ▸ ⟨m₀, rfl⟩
  have hgα : g⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hgst)
  have hαβ₁ := (adj_smul_inv_baseB h hgst hβδ).1
  have hst : (puAmalgam h.le).ofA.range = stab (puAmalgam h.le) (baseA _) := ofA_range_eq h.le
  have hTβ : Qv _ (baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ (adj_baseA_baseB _).symm
  have hT₁ : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    qv_le_stab_of_adj _ hαβ₁.symm
  have hZst := zHat_le_stab h hc hβ
  have hvT : vIm h.le a (Qv _ (baseB (puAmalgam h.le))) = MSP.qPoint (F ∙ v) := by
    rw [puAmalgam.qv_baseB, vIm_imM h, hT]
  have hvT₁ : vIm h.le a (Qv _ (g⁻¹ • baseB (puAmalgam h.le))) = MSP.qPoint (F ∙ w) := by
    rw [qv_smul, show g⁻¹ = (puAmalgam h.le).ofA m₀⁻¹ by rw [hg, map_inv], vIm_map_conj, hvT,
      map_inv, hm₀, inv_inv, MSP.qPoint_map_conj, Submodule.map_span, Set.image_singleton,
      Matrix.mulVecLin_apply]
  have hJ₁ : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (g⁻¹ • baseB (puAmalgam h.le)) =
      Qv _ (g⁻¹ • baseB (puAmalgam h.le)) := by
    have e := jOff_smul h.le hLn (2 ^ k) g⁻¹ (baseA (puAmalgam h.le)) (baseB _)
    rw [hgα] at e
    rw [e, hJ, qv_smul]
  have hJδ : jOff h.le L (2 ^ k) δ (baseB (puAmalgam h.le)) = Qv _ (baseB (puAmalgam h.le)) := by
    obtain ⟨y, hy, hyα⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)).symm hβδ
    have hyβ : y • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 hy
    rw [← hyα, ← hyβ, jOff_smul h.le hLn, hJ, ← qv_smul, hyβ]
  have hJα₁ : jOff h.le L (2 ^ k) (g⁻¹ • δ) (g⁻¹ • baseB (puAmalgam h.le)) =
      Qv _ (g⁻¹ • baseB (puAmalgam h.le)) := by
    rw [jOff_smul h.le hLn, hJδ, qv_smul]
  have hA : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ⊔ zHat _ (baseA (puAmalgam h.le)) α' =
      stab _ (baseA (puAmalgam h.le)) := by
    refine qv_sup_zHat_eq_stab h hd hc hβ hgst ?_
    rw [vIm_sup h.le (hT₁.trans hst.ge) (hZst.trans hst.ge), hvT₁]
    exact qPoint_sup_eq_top_of_transv_mem hw0 hc0 hvw htZ
  have hTT : Qv _ (baseB (puAmalgam h.le)) ⊔ Qv _ (g⁻¹ • baseB (puAmalgam h.le)) =
      stab _ (baseA (puAmalgam h.le)) := by
    refine (lift56 h hd (sup_le hTβ hT₁)
      ((qv_le_qv _ hyp hα (adj_baseA_baseB _)).trans le_sup_left)).2 ?_
    rw [vIm_sup h.le (hTβ.trans hst.ge) (hT₁.trans hst.ge), hvT, hvT₁]
    exact MSP.qPoint_sup_qPoint_eq_top (MSP.isPoint_span hv) (MSP.isPoint_span hw0) hopp
  have hB : ZH _ (baseB (puAmalgam h.le)) ⊓ Subgroup.centralizer
      (Qv _ (g⁻¹ • baseB (puAmalgam h.le)) : Set (puAmalgam h.le).Universal) ≤
        stabCenter _ (baseA (puAmalgam h.le)) := by
    rintro z ⟨hzZ, hzC⟩
    have hzst : z ∈ stab _ (baseA (puAmalgam h.le)) :=
      hTβ (omegaOneCenterOf_le _ hzZ)
    have hle : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.centralizer {z} := by
      rw [← hTT]
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (zh_le_centralizer _ _ hzZ) y hy)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hzC y hy)
    refine ⟨⟨z, hzst⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle y.2)
  refine ⟨g, hgst, 1, one_mem _, ⟨hA, ?_⟩, ⟨?_, ?_⟩, Or.inl ?_⟩
  · rw [rconj_one]
    refine le_antisymm (sup_le hT₁ (zm_le_stab_of_isCritical _ hyp h.critDist_pos hc)) ?_
    rw [← hA]
    exact sup_le_sup_left inf_le_left _
  · rw [hJ₁]
    exact hB
  · rw [rconj_one, hJ₁]
    exact hB
  · rw [rconj_one, hJα₁, hA, inf_idem]
    exact puTrans_le_stab h.le L _

end PointCase

end S5

end CFSG.Quasithin.MS93

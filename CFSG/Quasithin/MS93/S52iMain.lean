module

public import CFSG.Quasithin.MS93.S52iChief
public import CFSG.Quasithin.MS93.S52iQ3
public import CFSG.Quasithin.MS93.S5B58A
public import CFSG.Quasithin.MS93.S5Q2Hat
public import CFSG.Quasithin.MS93.S5A52Stmt
public import CFSG.Quasithin.MS93.S52i33
public import CFSG.Quasithin.MS93.S52iCount

public section

namespace CFSG.Quasithin.MS93.S52i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S33
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem le_normalizer_pre (hTM : T ≤ M) {K : Subgroup (puAmalgam hTM).Universal}
    (hK : stab (puAmalgam hTM) (baseA _) ≤ Subgroup.normalizer (K : Set _)) :
    M ≤ Subgroup.normalizer (pre hTM K : Set G) := by
  intro m hm
  have hmS : (puAmalgam hTM).ofA ⟨m, hm⟩ ∈ stab (puAmalgam hTM) (baseA _) := by
    rw [puAmalgam.stab_baseA hTM]
    exact ⟨⟨m, hm⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨x', hx', rfl⟩ := (mem_pre_iff' hTM).1 hx
    refine (mem_pre_iff' hTM).2 ⟨⟨m, hm⟩ * x' * ⟨m, hm⟩⁻¹, ?_, by simp⟩
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hK hmS) _).1 hx'
  · intro hx
    obtain ⟨y, hy, hyx⟩ := (mem_pre_iff' hTM).1 hx
    have hxM : x ∈ M := by
      have : m * x * m⁻¹ ∈ M := hyx ▸ y.2
      have e : x = m⁻¹ * (m * x * m⁻¹) * m := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (M.inv_mem hm) this) hm
    refine (mem_pre_iff' hTM).2 ⟨⟨x, hxM⟩, ?_, rfl⟩
    have hy' : (puAmalgam hTM).ofA y =
        (puAmalgam hTM).ofA ⟨m, hm⟩ * (puAmalgam hTM).ofA ⟨x, hxM⟩ *
          ((puAmalgam hTM).ofA ⟨m, hm⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hyx
    rw [hy'] at hy
    exact (Subgroup.mem_normalizer_iff.1 (hK hmS) _).2 hy

omit [Finite G] in
theorem pre_mono' (hTM : T ≤ M) {K K' : Subgroup (puAmalgam hTM).Universal} (hKK : K ≤ K') :
    pre hTM K ≤ pre hTM K' :=
  Subgroup.map_mono (Subgroup.comap_mono hKK)

theorem card_vIm_eq (h : PUHyp M T L) {k : ℕ} {F : Type} [Field F] [Fintype F]
    {a : ↥M →* ↥(StatedSp 2 F)} (hd : S5.IsSp4Data M T L k F a)
    {K : Subgroup (puAmalgam h.le).Universal} (hKS : K ≤ imM h.le M) (hK2 : IsPGroup 2 ↥K) :
    Nat.card ↥(S5.vIm h.le a K) = (Qv (puAmalgam h.le) (baseA _)).relIndex K := by
  have hpre2 : IsPGroup 2 ↥(pre h.le K) := by
    have h1 : IsPGroup 2 ↥(K.comap (puAmalgam h.le).ofA) :=
      hK2.comap_of_injective _ (puAmalgam h.le).ofA_injective
    exact h1.map M.subtype
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, ← imM_pre h.le hKS,
    relIndex_imM h.le (pre_le h.le _), vIm_eq_map_pre h a, imM_pre h.le hKS,
    ← S5.IsSp4Data.card_imSp_of_isPGroup hd h hpre2 (pre_le h.le _)]
  rfl

theorem critR_le_zm (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    critR (puAmalgam h.le) (baseA _) α' ≤ ZM (puAmalgam h.le) (baseA _) := by
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ h.hyp20
  have hd : (puAmalgam h.le).treeGraph.dist α' (baseA _) ≤ critDist (puAmalgam h.le) := by
    rw [tdist_comm]
    exact hc.2.1.le
  exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_dist_le _ hα' h.critDist_pos hd).trans
    (stab_le_normalizer_zm _ _))

theorem zHat_big (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hΛ : (2 ^ k) ^ 2 ≤ (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _))) :
    (2 ≤ k → (2 ^ k) ^ 2 ≤ Nat.card ↥(S5.imSp a (pre h.le (S5.zHat _ (baseA _) α')))) ∧
      (k = 1 → ∃ z : ↥M, (z : G) ∈ pre h.le (S5.zHat _ (baseA _) α') ∧ a z ≠ 1 ∧
        a z ∈ commutator (MSP.Sp4 F)) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have : CharP F 2 := S5.IsSp4Data.charP hd
  have hk1 := hd.1
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ h20
  have hq2 : 2 ^ k < (2 ^ k) ^ 2 := by
    have : 2 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk1)
    nlinarith
  have hΛ' : (2 ^ k) ^ 2 ≤ (Qv (puAmalgam h.le) (baseA _)).relIndex (ZM _ α') := by
    rcases S33.shape_of_sp4Data h hd hc with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
    · omega
    · exact h2
  have hZS : ZM (puAmalgam h.le) α' ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact zm_le_stab_of_dist_le _ hα' hb0 (by rw [tdist_comm]; exact hc.2.1.le)
  have hEA := isElemAbelian_zm _ h20 hb0 hα'
  have hZ2 : ∀ K : Subgroup (puAmalgam h.le).Universal, K ≤ ZM _ α' → IsPGroup 2 ↥K :=
    fun K hK x => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow]
      exact hEA.2 _ (hK x.2))⟩
  have himSp : ∀ K : Subgroup (puAmalgam h.le).Universal,
      S5.imSp a (pre h.le K) = S5.vIm h.le a K := fun K => (vIm_eq_map_pre h a K).symm
  have hmem : ∀ g ∈ S5.vIm h.le a (S5.zHat _ (baseA _) α'),
      ∃ z : ↥M, (z : G) ∈ pre h.le (S5.zHat _ (baseA _) α') ∧ a z = g := by
    rintro g ⟨z, hz, rfl⟩
    exact ⟨z, (mem_pre_iff h.le z).2 hz, rfl⟩
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · rw [himSp, S33.zHat_eq_of_two_le h hd hk hc, card_vIm_eq h hd hZS (hZ2 _ le_rfl)]
    exact hΛ'
  · subst hk
    have hq : Nat.card F = 2 := by rw [S5.IsSp4Data.nat_card_eq hd, pow_one]
    obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hq
    by_cases hhat : ∃ t : (puAmalgam h.le).Universal × (puAmalgam h.le).Universal ×
        (puAmalgam h.le).Universal, S5.IsHatTriple _ (baseA _) α' t.1 t.2.1 t.2.2 ∧
        t.2.2 ∉ Subgroup.closure ({t.1, t.2.1} : Set (puAmalgam h.le).Universal) ⊔ Qv _ α'
    · obtain ⟨⟨t₁, t₂, t₃⟩, ht, hn⟩ := hhat
      have hcomm := S5.hatEven_holds G M T L h hmin hb 1 F _ _ a hd α' hc t₁ t₂ t₃ ht hn
      have hZh := S5.zHat_eq_of_isHatTriple h hd hq hc ht hn
      obtain ⟨v₁, v₂, hv₁, hv₂, hv12, -, -, -, hmemZ⟩ :=
        S5.hat_shape h hd hq hc ht hZh (by simpa using hΛ')
      have hne1 : ∀ v : MSP.V4 F, v ≠ 0 → MSP.transv v 1 ≠ 1 := fun v hv h1 =>
        one_ne_zero (MSP.transv_injective hv (h1.trans (MSP.transv_zero v).symm))
      have hne12 : MSP.transv v₁ 1 * MSP.transv v₂ 1 ≠ 1 := by
        intro h1
        have h2 : MSP.transv v₂ 1 = (MSP.transv v₁ 1)⁻¹ := (eq_inv_of_mul_eq_one_right h1)
        rw [MSP.transv_inv, CharTwo.neg_eq] at h2
        exact hv12 ((MSP.transv_eq_transv_iff hv₁).1 h2).symm
      obtain ⟨g, hg, hg1⟩ : ∃ g ∈ S5.vIm h.le a (S5.zHat _ (baseA _) α'), g ≠ 1 := by
        rcases hmemZ with h1 | h1 | h1
        · exact ⟨_, h1, hne1 v₁ hv₁⟩
        · exact ⟨_, h1, hne1 v₂ hv₂⟩
        · exact ⟨_, h1, hne12⟩
      obtain ⟨z, hz, rfl⟩ := hmem g hg
      exact ⟨z, hz, hg1, hcomm hg⟩
    · have hZh : S5.zHat (puAmalgam h.le) (baseA _) α' = ZM _ α' := by
        unfold S5.zHat
        refine le_antisymm inf_le_left (le_inf le_rfl (le_iInf fun t => le_iInf fun ht =>
          le_iInf fun hn => absurd ⟨t, ht, hn⟩ hhat))
      set A := S5.vIm h.le a (S5.zHat _ (baseA _) α') with hA
      have hcard : 4 ≤ Nat.card A := by
        rw [hA, hZh, card_vIm_eq h hd hZS (hZ2 _ le_rfl)]
        simpa using hΛ'
      obtain ⟨g, hg, hgD, hg1⟩ : ∃ g ∈ A, g ∈ commutator (MSP.Sp4 F) ∧ g ≠ 1 := by
        by_contra hall
        push Not at hall
        have hinf : commutator (MSP.Sp4 F) ⊓ A = ⊥ := by
          rw [eq_bot_iff]
          intro g hg
          exact hall g hg.2 hg.1
        have h1 := Subgroup.relIndex_mul_card (H := commutator (MSP.Sp4 F)) (K := A)
        rw [hinf, Subgroup.card_bot, mul_one] at h1
        have h2 : (commutator (MSP.Sp4 F)).relIndex A ≤ 2 := by
          have h3 := Subgroup.relIndex_le_of_le_right (H := commutator (MSP.Sp4 F))
            (le_top : A ≤ ⊤) (by rw [Subgroup.relIndex_top_right, MSP.index_commutator c]; norm_num)
          rwa [Subgroup.relIndex_top_right, MSP.index_commutator c] at h3
        rw [h1] at h2
        have h4 : Nat.card ↥A ≤ 2 := h2
        have h5 : 4 ≤ Nat.card ↥A := hcard
        omega
      obtain ⟨z, hz, rfl⟩ := hmem g hg
      exact ⟨z, hz, hg1, hgD⟩

theorem s52i_of
    (h14 : MS14AS) (hSQ : SQTKQuot) : S5.S52i := by
  intro G _ _ M T L h hmin hb k F _ _ a hd α' hc hΛ
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hk1 := hd.1
  have hα : IsMVtx (puAmalgam h.le) (baseA _) := PU.isMVtx_baseA _
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ h20
  have hLt : puTrans h.le L (baseA _) = imM h.le L :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)
  have hVQ : Vv (puAmalgam h.le) (baseA _) ≤ Qv _ (baseA _) := S38E.vv_le_qv _ hb hα
  have hVS : Vv (puAmalgam h.le) (baseA _) ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact hVQ.trans (qv_le_stab _ _)
  refine ⟨fun hle => ?_, fun A B C hZA hAB hBC hCV hAn hBn hCn => ?_⟩
  ·
    obtain ⟨δ, hδ, hδB⟩ := S5B.exists_uSub_not_le_bSub h hb
    apply hδB
    have hδM : IsMVtx _ δ := by
      have := (isMVtx_iff_of_adj _ hδ).not.mp (not_isMVtx_baseB _)
      simpa using this
    have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ ≤ 2 := by
      have h1 := dist_triangle (puAmalgam h.le) (baseA _) (baseB _) δ
      rw [dist_eq_one_of_adj _ (adj_baseA_baseB _), dist_eq_one_of_adj _ hδ] at h1
      exact h1
    have hZV : ZM (puAmalgam h.le) δ ≤ Vv _ (baseA _) := by
      rw [← zv_of_isMVtx _ hδM]
      exact le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
        (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2}) => Zv (puAmalgam h.le) ρ) δ hdδ le_rfl
    refine (S5B.uSub_le_zm h.le δ).trans (hZV.trans fun v hv => ?_)
    exact Subgroup.subset_closure ⟨hv, fun y hy => hle (Subgroup.commutator_mem_commutator hv hy)⟩
  set δ₂ := geo (puAmalgam h.le) α' (baseA _) 2 with hδ₂
  have hdα : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) := by
    rw [tdist_comm]
    exact hc.2.1
  have h2le : 2 ≤ (puAmalgam h.le).treeGraph.dist α' (baseA _) := by omega
  have hδ₂M : IsMVtx _ δ₂ := (isMVtx_geo _ h2le).2 (iff_of_true hα' even_two)
  have hadj12 : (puAmalgam h.le).treeGraph.Adj (geo (puAmalgam h.le) α' (baseA _) 1) δ₂ :=
    adj_geo _ (show 1 < (puAmalgam h.le).treeGraph.dist α' (baseA _) by omega)
  set Y := Vv (puAmalgam h.le) (baseA _) ⊓ Qv _ δ₂ with hY
  have hYT : Y ≤ Qv _ (geo (puAmalgam h.le) α' (baseA _) 1) :=
    inf_le_right.trans (qv_le_qv _ h20 hδ₂M hadj12.symm)
  have hYR : Y ≤ Subgroup.centralizer (critR (puAmalgam h.le) (baseA _) α' : Set _) := by
    have hQZ : Qv (puAmalgam h.le) (baseA _) ≤
        Subgroup.centralizer (ZM (puAmalgam h.le) (baseA _) : Set _) :=
      (qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le (zm_le_xm _ h20 hb0 hα))
    exact inf_le_left.trans (hVQ.trans (hQZ.trans (Subgroup.centralizer_le (critR_le_zm h hc))))
  have hYZ : ⁅Y, S5.zHat (puAmalgam h.le) (baseA _) α'⁆ ≤ ZM (puAmalgam h.le) (baseA _) :=
    (commutator_zHat_le_critR_of_sq h hd hc hΛ hYT hYR).trans (critR_le_zm h hc)
  have hZS : ZM (puAmalgam h.le) α' ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact zm_le_stab_of_dist_le _ hα' hb0 hdα.le
  have hEA := isElemAbelian_zm _ h20 hb0 hα'
  set Vp := pre h.le (Vv (puAmalgam h.le) (baseA _)) with hVp
  set Yp := pre h.le Y with hYp
  set Ep := pre h.le (S5.zHat (puAmalgam h.le) (baseA _) α') with hEp
  set Zp := pre h.le (ZM (puAmalgam h.le) (baseA _)) with hZp
  have hV2 : IsPGroup 2 ↥Vp := by
    obtain ⟨ρ, hρ⟩ := exists_adj (puAmalgam h.le) (baseA _)
    have hρH : ¬ IsMVtx (puAmalgam h.le) ρ := by have := isMVtx_iff_of_adj _ hρ; tauto
    have hV2' : IsPGroup 2 ↥(Vv (puAmalgam h.le) (baseA _)) :=
      ((isPGroup_qv _ h20 hρH).to_le (qv_le_qv _ h20 hα hρ)).to_le hVQ
    exact (hV2'.comap_of_injective _ (puAmalgam h.le).ofA_injective).map M.subtype
  have hZhZ : S5.zHat (puAmalgam h.le) (baseA _) α' ≤ ZM _ α' := inf_le_left
  have hEab : ∀ x ∈ Ep, ∀ y ∈ Ep, x * y = y * x :=
    pre_comm h.le fun x hx y hy =>
      (isMulCommutative_subgroup_iff.mp hEA.1) x (hZhZ hx) y (hZhZ hy)
  have hE2 : ∀ x ∈ Ep, x ^ 2 = 1 := pre_sq h.le fun x hx => hEA.2 x (hZhZ hx)
  have hYE : ∀ y ∈ Yp, ∀ e ∈ Ep, e * y * e⁻¹ * y⁻¹ ∈ Zp := by
    intro y hy e he
    obtain ⟨y', hy', rfl⟩ := (mem_pre_iff' h.le).1 hy
    obtain ⟨e', he', rfl⟩ := (mem_pre_iff' h.le).1 he
    refine (mem_pre_iff' h.le).2 ⟨e' * y' * e'⁻¹ * y'⁻¹, ?_, by simp⟩
    have hc' : (puAmalgam h.le).ofA (e' * y' * e'⁻¹ * y'⁻¹) =
        ⁅(puAmalgam h.le).ofA y', (puAmalgam h.le).ofA e'⁆⁻¹ := by
      rw [commutatorElement_inv, commutatorElement_def]
      simp [map_mul, map_inv]
    rw [hc']
    exact Subgroup.inv_mem _ (hYZ (Subgroup.commutator_mem_commutator hy' he'))
  have hYV : Yp.relIndex Vp ≤ (2 ^ k) ^ 3 := by
    rw [hYp, hVp, relIndex_pre h.le _ (pre_le h.le _), imM_pre h.le hVS, hY, inf_comm,
      Subgroup.inf_relIndex_right]
    exact relIndex_qv_geo_two_vv_le h hd hb hc
  have hAS : A ≤ imM h.le M := hAB.trans (hBC.trans (hCV.trans hVS))
  have hBS : B ≤ imM h.le M := hBC.trans (hCV.trans hVS)
  have hCS : C ≤ imM h.le M := hCV.trans hVS
  have hcomm : ∀ {P Q : Subgroup (puAmalgam h.le).Universal}, P ≤ imM h.le M →
      Q ≤ imM h.le M → (⁅pre h.le Q, L⁆ ≤ pre h.le P ↔ ⁅Q, puTrans h.le L (baseA _)⁆ ≤ P) := by
    intro P Q hP hQ
    rw [← imM_le_imM_iff h.le (commutator_le_of_le (pre_le h.le _) h.L_le),
      imM_commutator h.le (pre_le h.le _) h.L_le, imM_pre h.le hQ, imM_pre h.le hP, hLt]
  have hres := le_or_le_of_count h.L_le h.perfect (V := Vp) (Y := Yp) (Z := Zp)
    (pre_le h.le _) (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk1)) hYV
    (fun N W hNn hWn hZN hNW hWV hWN hch =>
      le_relIndex_of_chief h14 hSQ h hd (pre_le h.le _) hV2 (pre_le h.le _) hEab hE2
        (zHat_big h hmin hb hd hc hΛ) hNn hWn hNW hWV hWN hch
        (fun y hy e he => hZN (hYE y hy.2 e he)))
    (le_normalizer_pre h.le hAn) (le_normalizer_pre h.le hBn) (le_normalizer_pre h.le hCn)
    (pre_mono' h.le hZA) (pre_mono' h.le hAB) (pre_mono' h.le hBC) (pre_mono' h.le hCV)
  rcases hres with h1 | h1
  · exact Or.inl ((hcomm hAS hBS).1 h1)
  · exact Or.inr ((hcomm hBS hCS).1 h1)

end CFSG.Quasithin.MS93.S52i

module

public import CFSG.Quasithin.MS93.S5BBasic
public import CFSG.Quasithin.MS93.S5BEqv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S5B

theorem commutator_commutator_le_of_rotate {Γ : Type*} [Group Γ] {N H₁ H₂ H₃ : Subgroup Γ}
    (hn₁ : H₁ ≤ Subgroup.normalizer (N : Set Γ)) (hn₂ : H₂ ≤ Subgroup.normalizer (N : Set Γ))
    (hn₃ : H₃ ≤ Subgroup.normalizer (N : Set Γ)) (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ ≤ N)
    (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ ≤ N) : ⁅⁅H₁, H₂⁆, H₃⁆ ≤ N := by
  have hconj : ∀ g ∈ Subgroup.normalizer (N : Set Γ), ∀ n ∈ N, g * n * g⁻¹ ∈ N :=
    fun g hg n hn => (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have key : ∀ w ∈ ⁅H₁, H₂⁆, w ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ z ∈ H₃, ⁅w, z⁆ ∈ N := by
    intro w hw
    have hw' : w ∈ Subgroup.closure {g : Γ | ∃ g₁ ∈ H₁, ∃ g₂ ∈ H₂, ⁅g₁, g₂⁆ = g} := hw
    clear hw
    induction hw' using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hw
      refine ⟨?_, fun z hz => ?_⟩
      · have hxN := hn₁ hx
        have hyN := hn₂ hy
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hxN hyN) (inv_mem hxN)) (inv_mem hyN)
      · have hu : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h2 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₃.inv_mem hz) (H₁.inv_mem hx)) hy))
        have hv : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ ∈ N := by
          rw [← commutatorElement_inv]
          exact N.inv_mem (h1 (Subgroup.commutator_mem_commutator
            (Subgroup.commutator_mem_commutator (H₂.inv_mem hy) hz) (H₁.inv_mem hx)))
        have hxz := mul_mem (hn₁ hx) (hn₃ hz)
        have hxy := mul_mem (hn₁ hx) (hn₂ hy)
        have e1 : ⁅⁅x, y⁆, z⁆ = (x * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ * (x * y)⁻¹) *
            (x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ * (x * z)⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e1]
        exact mul_mem (hconj _ hxy _ hv) (hconj _ hxz _ hu)
    | one => exact ⟨one_mem _, fun z _ => by simp⟩
    | mul a b _ _ iha ihb =>
      refine ⟨mul_mem iha.1 ihb.1, fun z hz => ?_⟩
      have e1 : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (hconj _ iha.1 _ (ihb.2 z hz)) (iha.2 z hz)
    | inv a _ iha =>
      refine ⟨inv_mem iha.1, fun z hz => ?_⟩
      have e1 : ⁅a⁻¹, z⁆ = a⁻¹ * (⁅a, z⁆)⁻¹ * a := by
        simp only [commutatorElement_def]
        group
      rw [e1]
      have := hconj _ (inv_mem iha.1) _ (N.inv_mem (iha.2 z hz))
      simpa using this
  exact Subgroup.commutator_le.mpr fun w hw z hz => (key w hw).2 z hz

theorem commutator_le_of_perfect {Γ : Type*} [Group Γ] {W L X U : Subgroup Γ}
    (hL : ⁅L, L⁆ = L) (hWU : W ≤ Subgroup.normalizer (U : Set Γ))
    (hLU : L ≤ Subgroup.normalizer (U : Set Γ)) (hWL : ⁅W, L⁆ ≤ X) (hXL : ⁅X, L⁆ ≤ U) :
    ⁅W, L⁆ ≤ U := by
  have h1 : ⁅⁅L, W⁆, L⁆ ≤ U := by
    rw [Subgroup.commutator_comm L W]
    exact (Subgroup.commutator_mono hWL le_rfl).trans hXL
  have h2 : ⁅⁅W, L⁆, L⁆ ≤ U := (Subgroup.commutator_mono hWL le_rfl).trans hXL
  have key := commutator_commutator_le_of_rotate (N := U) (H₁ := L) (H₂ := L) (H₃ := W)
    hLU hLU hWU h1 h2
  rwa [hL, Subgroup.commutator_comm] at key

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem commutator_le_of_baseA (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {Z₀ : Subgroup (puAmalgam h.le).Universal}
    (hZ₀n : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (Z₀ : Set _))
    (hZ₀X : Z₀ ≤ XM _ (baseA (puAmalgam h.le)))
    (hXZ₀ : ⁅XM _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ ≤ Z₀)
    {μ : Vtx (puAmalgam h.le)} (hμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2)
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ XM _ μ)
    (hn : puTrans h.le L (baseA _) ≤ Subgroup.normalizer ((Y ⊔ Z₀ : Subgroup _) : Set _)) :
    ⁅Y ⊔ Z₀, puTrans h.le L (baseA _)⁆ ≤ Z₀ := by
  have hyp := h.hyp20
  have hC := h.centHyp
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hμM : IsMVtx _ μ := ((even_dist_iff _ _ μ).1 (by rw [hμ]; exact even_two)).1 hα
  have hLα : puTrans h.le L (baseA _) = imM h.le L :=
    puTrans_baseA h.le ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer)
  have hQα : Qv _ (baseA (puAmalgam h.le)) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have hαγ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA _) μ 1) :=
    adj_geo_one _ (by rw [hμ]; norm_num)
  have hγμ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA _) μ 1) μ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := μ) (i := 1) (by rw [hμ]; norm_num)
    rwa [show (1 + 1 : ℕ) = 2 from rfl, ← hμ, geo_dist] at this
  have hγ : ¬ IsMVtx _ (geo _ (baseA (puAmalgam h.le)) μ 1) := (isMVtx_iff_of_adj _ hαγ).1 hα
  have hQμγ : Qv _ μ ≤ Qv _ (geo _ (baseA (puAmalgam h.le)) μ 1) := qv_le_qv _ hyp hμM hγμ.symm
  have hXμQ : XM _ μ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    ms22_i _ hyp hC hμM hα (by rw [SimpleGraph.dist_comm, hμ]; exact hb)
  have hZ₀Q : Z₀ ≤ Qv _ (baseA (puAmalgam h.le)) := hZ₀X.trans (xm_le_qv _ _)
  have hQst : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ (baseA _) := qv_le_stab _ _
  have hstM : stab _ (baseA (puAmalgam h.le)) = (puAmalgam h.le).ofA.range := by
    rw [puAmalgam.stab_baseA, imM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  by_cases hQ : Qv _ μ ≤ Qv _ (baseA (puAmalgam h.le))
  ·
    have : Finite ↥(Qv _ (baseA (puAmalgam h.le))) := by rw [hQα]; exact finite_imM h.le _
    have hQe : Qv _ μ = Qv _ (baseA (puAmalgam h.le)) :=
      Subgroup.eq_of_le_of_card_ge hQ (card_qv_eq h hμM).symm.le
    have hYX : Y ≤ XM _ (baseA (puAmalgam h.le)) := by
      have : XM _ μ = XM _ (baseA (puAmalgam h.le)) := by simp only [XM, hQe]
      rw [← this]
      exact hY
    exact (Subgroup.commutator_mono (sup_le hYX hZ₀X) le_rfl).trans hXZ₀
  · obtain ⟨y, hyμ, hyα⟩ := Set.not_subset.1 hQ
    have hyst : y ∈ stab _ (baseA (puAmalgam h.le)) :=
      qv_le_stab_of_isMVtx _ hyp hα hαγ (hQμγ hyμ)
    rw [hstM] at hyst
    obtain ⟨y₀, rfl⟩ := hyst
    have hyZ : (puAmalgam h.le).ofA y₀ ∈ Subgroup.normalizer (Z₀ : Set (puAmalgam h.le).Universal) :=
      hZ₀n (by rw [hstM]; exact ⟨y₀, rfl⟩)
    have hWst : Y ⊔ Z₀ ≤ stab _ (baseA (puAmalgam h.le)) :=
      (sup_le (hY.trans hXμQ) hZ₀Q).trans hQst
    have hZst : Z₀ ≤ stab _ (baseA (puAmalgam h.le)) := hZ₀Q.trans hQst
    have hWW := imM_preM h.le hWst
    have hZZ := imM_preM h.le hZst
    have hWn₀ : L ≤ Subgroup.normalizer (preM h.le (Y ⊔ Z₀) : Set G) :=
      le_normalizer_preM h.le h.L_le (hLα ▸ hn)
    have hZn₀ : M ≤ Subgroup.normalizer (preM h.le Z₀ : Set G) := by
      refine le_normalizer_preM h.le le_rfl ?_
      rw [← puAmalgam.stab_baseA]
      exact hZ₀n
    have hYn : Y ≤ Subgroup.normalizer (Z₀ : Set _) := (hY.trans hXμQ).trans (hQst.trans hZ₀n)
    have hyW : ∀ w ∈ Y ⊔ Z₀, (puAmalgam h.le).ofA y₀ * w *
        ((puAmalgam h.le).ofA y₀)⁻¹ * w⁻¹ ∈ Z₀ := by
      intro w hw
      have hw' : w ∈ ((Y : Set (puAmalgam h.le).Universal) *
          (Z₀ : Set (puAmalgam h.le).Universal)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y _ hYn]
        exact hw
      obtain ⟨y', hy', z, hz, rfl⟩ := hw'
      have hcy : (puAmalgam h.le).ofA y₀ * y' = y' * (puAmalgam h.le).ofA y₀ :=
        (Subgroup.mem_centralizer_iff.1 (qv_le_centralizer_xm _ μ hyμ) y' (hY hy')).symm
      have hz' : (puAmalgam h.le).ofA y₀ * z * ((puAmalgam h.le).ofA y₀)⁻¹ * z⁻¹ ∈ Z₀ :=
        mul_mem ((Subgroup.mem_normalizer_iff.1 hyZ z).1 hz) (inv_mem hz)
      have e : (puAmalgam h.le).ofA y₀ * (y' * z) * ((puAmalgam h.le).ofA y₀)⁻¹ * (y' * z)⁻¹ =
          y' * ((puAmalgam h.le).ofA y₀ * z * ((puAmalgam h.le).ofA y₀)⁻¹ * z⁻¹) * y'⁻¹ := by
        rw [← mul_assoc, hcy]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.1 (hYn hy') _).1 hz'
    have hcore := commutator_le_of_two_elt h
      (W := preM h.le (Y ⊔ Z₀)) (Z := preM h.le Z₀) hWn₀ (h.L_le.trans hZn₀) y₀.2 ?_ ?_
      (hZn₀ y₀.2) ?_
    · have := (commutator_imM_le_iff h.le (preM_le h.le _) h.L_le).2 hcore
      rwa [hWW, ← hLα, hZZ] at this
    ·
      obtain ⟨e, he⟩ := isPGroup_qv _ hyp hγ ⟨_, hQμγ hyμ⟩
      refine ⟨e, ?_⟩
      have he' : (puAmalgam h.le).ofA (y₀ ^ 2 ^ e) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val he
      have := (puAmalgam h.le).ofA_injective (he'.trans (map_one _).symm)
      simpa using congrArg Subtype.val this
    · intro hO
      apply hyα
      rw [hQα]
      exact ⟨y₀, Subgroup.mem_subgroupOf.2 hO, rfl⟩
    · rintro _ ⟨m, hm, rfl⟩
      have h2 : (puAmalgam h.le).ofA (y₀ * m * y₀⁻¹ * m⁻¹) ∈ Z₀ := by
        simpa [map_mul, map_inv] using hyW _ hm
      have hgoal := (mem_preM h.le (y₀ * m * y₀⁻¹ * m⁻¹)).2 h2
      simpa using hgoal

theorem commutator_le_uSub_baseA (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (h32 : ⁅Xq M, L⁆ ≤ Uq M T L) {μ : Vtx (puAmalgam h.le)}
    (hμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2)
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ XM _ μ)
    (hn : puTrans h.le L (baseA _) ≤
      Subgroup.normalizer ((Y ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    ⁅Y, puTrans h.le L (baseA _)⁆ ≤ S5.uSub h.le L (baseA _) := by
  have hb0 := h.critDist_pos
  have hXU : ⁅XM _ (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ ≤
      S5.uSub h.le L (baseA _) := by
    rw [xm_baseA_eq h, puTrans_L_baseA h, uSub_baseA h]
    exact (commutator_imM_le_iff h.le (Xq_le M) h.L_le).2 h32
  have hUX : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ XM _ (baseA _) :=
    (commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L (baseA _)).trans
      (stab_le_normalizer_zm _ _))).trans (zm_le_xm _ h.hyp20 hb0 (isMVtx_baseA _))
  have hW := commutator_le_of_baseA h hb (Z₀ := XM _ (baseA (puAmalgam h.le)))
    (stab_le_normalizer_xm _ _) le_rfl (hXU.trans hUX) hμ hY hn
  have hLst := puTrans_le_stab h.le L (baseA (puAmalgam h.le))
  have hUn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.uSub h.le L (baseA _) : Set _) :=
    le_normalizer_commutator (stab_le_normalizer_zm _ _)
      (stab_le_normalizer_puTrans h.le
        ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer) _)
  have hXμst : XM _ μ ≤ stab _ (baseA (puAmalgam h.le)) := by
    have hμM : IsMVtx _ μ :=
      ((even_dist_iff _ _ μ).1 (by rw [hμ]; exact even_two)).1 (isMVtx_baseA _)
    exact (ms22_i _ h.hyp20 h.centHyp hμM (isMVtx_baseA _)
      (by rw [SimpleGraph.dist_comm, hμ]; exact hb)).trans (qv_le_stab _ _)
  have hperf : ⁅puTrans h.le L (baseA (puAmalgam h.le)), puTrans h.le L (baseA _)⁆ =
      puTrans h.le L (baseA _) := by
    rw [puTrans_L_baseA h, ← imM_commutator h.le h.L_le h.L_le, h.perfect]
  have key := commutator_le_of_perfect (W := Y ⊔ XM _ (baseA (puAmalgam h.le)))
    (L := puTrans h.le L (baseA _)) (X := XM _ (baseA (puAmalgam h.le)))
    (U := S5.uSub h.le L (baseA _)) hperf ?_ (hLst.trans hUn) hW hXU
  · exact (Subgroup.commutator_mono le_sup_left le_rfl).trans key
  · exact (sup_le (hY.trans hXμst) (xm_le_qv _ _ |>.trans (qv_le_stab _ _))).trans hUn

theorem commutator_le_uSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (h32 : ⁅Xq M, L⁆ ≤ Uq M T L) {δ μ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hμ : (puAmalgam h.le).treeGraph.dist δ μ = 2)
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ XM _ μ)
    (hn : puTrans h.le L δ ≤ Subgroup.normalizer ((Y ⊔ XM _ δ : Subgroup _) : Set _)) :
    ⁅Y, puTrans h.le L δ⁆ ≤ S5.uSub h.le L δ := by
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ (isMVtx_baseA _) hδ
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hLg := puTrans_smul (hTM := h.le) hLn g (baseA _)
  have hXg := xm_smul (puAmalgam h.le) g (baseA _)
  have hUg := uSub_smul h.le hLn g (baseA (puAmalgam h.le))
  have hμ' : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • μ) = 2 := by
    rw [← dist_smul _ g, smul_inv_smul]
    exact hμ
  have hXμ : XM (puAmalgam h.le) μ = (XM _ (g⁻¹ • μ)).map (MulAut.conj g).toMonoidHom := by
    rw [← xm_smul, smul_inv_smul]
  have hY' : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ XM _ (g⁻¹ • μ) := by
    rw [map_conj_le_iff, inv_inv, ← hXμ]
    exact hY
  have hn' : puTrans h.le L (baseA _) ≤ Subgroup.normalizer
      ((Y.map (MulAut.conj g⁻¹).toMonoidHom ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) :
        Set _) := by
    rw [hLg, hXg, map_conj_le_iff, ← normalizer_map_conj, Subgroup.map_sup,
      map_conj_inv_map_conj] at hn
    exact hn
  have key := commutator_le_uSub_baseA h hb h32 hμ' hY' hn'
  have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) key
  rwa [Subgroup.map_commutator, map_conj_map_conj_inv, ← hLg, ← hUg] at this

theorem le_bSub_of_xm (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (h32 : ⁅Xq M, L⁆ ≤ Uq M T L) {δ μ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    (hμ : (puAmalgam h.le).treeGraph.dist δ μ = 2)
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ XM _ μ) (hYV : Y ≤ Vv _ δ)
    (hn : puTrans h.le L δ ≤ Subgroup.normalizer ((Y ⊔ XM _ δ : Subgroup _) : Set _)) :
    Y ≤ S5.bSub h.le L δ := by
  have hc := commutator_le_uSub h hb h32 hδ hμ hY hn
  have hUZ : S5.uSub h.le L δ ≤ ZM _ δ :=
    commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L δ).trans
      (stab_le_normalizer_zm _ _))
  intro y hy
  refine Subgroup.subset_closure ⟨hYV hy, fun l hl => ?_⟩
  exact hUZ (hc (Subgroup.commutator_mem_commutator hy hl))

end S5B

end CFSG.Quasithin.MS93

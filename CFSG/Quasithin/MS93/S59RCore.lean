module

public import CFSG.Quasithin.MS93.S59RT
public import CFSG.Quasithin.MS93.S59C1

public section

namespace CFSG.Quasithin.MS93.S59R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Case1

theorem map_conj_le_centralizer {Γ : Type*} [Group Γ] {A B : Subgroup Γ} (g : Γ)
    (hAB : A ≤ Subgroup.centralizer (B : Set Γ)) :
    A.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup Γ) : Set Γ) := by
  rw [PU.centralizer_map_mulEquiv]
  exact Subgroup.map_mono hAB

theorem case1_core (h32 : S32) (hX2 : S33.S33X52) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {K : Subgroup (puAmalgam h.le).Universal} (hKst : K ≤ stab _ (baseA (puAmalgam h.le)))
    {α'' : Vtx (puAmalgam h.le)} (hc'' : IsCritical _ (baseA (puAmalgam h.le)) α'')
    {m : (puAmalgam h.le).Universal} (hm : m ∈ stab _ (baseA (puAmalgam h.le)))
    (hγ'' : geo _ (baseA (puAmalgam h.le)) α'' 2 = m • γ)
    (hgen : K ⊔ S5.zHat _ (baseA (puAmalgam h.le)) α'' = stab _ (baseA (puAmalgam h.le)))
    (hKH : ∀ x ∈ K, ¬ S59.hSub h.le L γ ≤
      Subgroup.centralizer (ZM _ (x⁻¹ • α'') : Set (puAmalgam h.le).Universal)) :
    False := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hyp := h.hyp20
  have hC := h.centHyp
  have h32' := (h32 G M T L h).2.1
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨hγ, hd2, -⟩ := S59.gamma_facts h hβγ hγα
  have hUγB := S59.uSub_not_le_bSub_of_hyp h hb' hd hβγ hγα hξ hξα hP
  obtain ⟨-, -, hZ''st, hRX, hXX, -⟩ := S5B.crit_facts h hc''
  have hTn := S59.le_normalizer_tZero h hb' (L := L) hαβ hβγ
  have hxα : ∀ x ∈ K, x⁻¹ • baseA (puAmalgam h.le) = baseA _ := fun x hx =>
    (mem_stab _).1 (inv_mem (hKst hx))
  have hcx : ∀ x ∈ K, IsCritical _ (baseA (puAmalgam h.le)) (x⁻¹ • α'') := by
    intro x hx
    have := (isCritical_smul _ x⁻¹ _ _).2 hc''
    rwa [hxα x hx] at this
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup (puAmalgam h.le).Universal,
      W = ⨆ x : ↥K, ZM _ ((x : (puAmalgam h.le).Universal) • γ) := ⟨_, rfl⟩
  have hgenW : ∀ x ∈ K, ZM _ (x • γ) ≤ W := fun x hx =>
    hWdef ▸ le_iSup_of_le (⟨x, hx⟩ : ↥K) le_rfl
  have hWle : ∀ {Y : Subgroup (puAmalgam h.le).Universal}, (∀ x ∈ K, ZM _ (x • γ) ≤ Y) → W ≤ Y :=
    fun hY => hWdef ▸ iSup_le fun x => hY x x.2
  have hdist : ∀ x ∈ K, (puAmalgam h.le).treeGraph.dist (baseA _) (x • γ) = 2 := by
    intro x hx
    rw [← (mem_stab _).1 (hKst hx), dist_smul]
    exact hd2
  have hdd'' : (puAmalgam h.le).treeGraph.dist (baseA _) α'' = critDist (puAmalgam h.le) :=
    hc''.2.1
  have hα''M : IsMVtx _ α'' := hc''.isMVtx_right _ hyp
  set σ₂ := geo _ α'' (baseA (puAmalgam h.le)) 2 with hσ₂def
  set σ₁ := geo _ α'' (baseA (puAmalgam h.le)) 1 with hσ₁def
  have hdσ₂α : (puAmalgam h.le).treeGraph.dist σ₂ (baseA _) = critDist (puAmalgam h.le) - 2 := by
    rw [dist_geo_right _ (by rw [SimpleGraph.dist_comm, hdd'']; omega), SimpleGraph.dist_comm,
      hdd'']
  have hσ₂M : IsMVtx _ σ₂ :=
    (isMVtx_geo _ (by rw [SimpleGraph.dist_comm, hdd'']; omega)).2 (iff_of_true hα''M ⟨1, rfl⟩)
  have hσ₁σ₂ : (puAmalgam h.le).treeGraph.Adj σ₁ σ₂ := by
    have := adj_geo _ (u := α'') (w := baseA (puAmalgam h.le)) (i := 1)
      (by rw [SimpleGraph.dist_comm, hdd'']; omega)
    rwa [show (1 + 1 : ℕ) = 2 from rfl] at this
  have hα''σ₁ : (puAmalgam h.le).treeGraph.Adj α'' σ₁ :=
    adj_geo_one _ (by rw [SimpleGraph.dist_comm, hdd'']; omega)
  have hW1 : W ≤ Subgroup.centralizer (ZM _ σ₂ : Set (puAmalgam h.le).Universal) := by
    refine hWle fun x hx => ?_
    have h1 := zm_le_centralizer_zm_geo h hb hd hβγ hγα hξ hξα hP (hcx x hx) (hKH x hx)
    have hgeo : geo _ (x⁻¹ • α'') (baseA (puAmalgam h.le)) 2 = x⁻¹ • σ₂ := by
      have := geo_smul _ x⁻¹ α'' (baseA (puAmalgam h.le)) 2
      rwa [hxα x hx] at this
    rw [hgeo] at h1
    have h2 := map_conj_le_centralizer x h1
    rw [← zm_smul, ← zm_smul, smul_inv_smul] at h2
    exact h2
  have hε : (puAmalgam h.le).treeGraph.Adj σ₂ (geo _ σ₂ (baseA (puAmalgam h.le)) 1) :=
    adj_geo_one _ (by rw [hdσ₂α]; omega)
  have hdαε : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ σ₂ (baseA (puAmalgam h.le)) 1) =
      critDist (puAmalgam h.le) - 3 := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by rw [hdσ₂α]; omega), hdσ₂α]
    omega
  have hWε : W ≤ Qv _ (geo _ σ₂ (baseA (puAmalgam h.le)) 1) := by
    refine hWle fun x hx => zm_le_qv_of_dist_lt _ ((isMVtx_smul _ x γ).2 hγ) ?_
    have t := dist_triangle _ (x • γ) (baseA (puAmalgam h.le))
      (geo _ σ₂ (baseA (puAmalgam h.le)) 1)
    rw [SimpleGraph.dist_comm (u := x • γ) (v := baseA _), hdist x hx, hdαε] at t
    omega
  have hWσ₂ : W ≤ Qv _ σ₂ := le_qv_of_le_centralizer _ hC hσ₂M hε hWε hW1
  have hWT : W ≤ Qv _ σ₁ := hWσ₂.trans (qv_le_qv _ hyp hσ₂M hσ₁σ₂.symm)
  have hWst'' : W ≤ stab _ α'' := hWT.trans (qv_le_stab_of_adj _ hα''σ₁.symm)
  have hAT : critA _ (baseA (puAmalgam h.le)) α'' ≤ S59.tZero h.le L γ := by
    rw [← S59.tZero_smul_eq h hb' hαβ hβγ hm]
    refine S59.xm_inf_le_tZero h ((isMVtx_smul _ m γ).2 hγ) ?_
    rw [← hγ'', dist_geo_right _ (by omega), hdd'']
    omega
  have hW2 : W ≤ Subgroup.centralizer ((S5.uSub h.le L α'' ⊓ Qv _ (baseA (puAmalgam h.le)) :
      Subgroup _) : Set (puAmalgam h.le).Universal) := by
    refine hWle fun x hx => ?_
    have hUx : S5.uSub h.le L γ ≤ stab _ (x⁻¹ • α'') := by
      intro u hu
      rw [mem_stab_smul, inv_inv]
      have hxu : x * u * x⁻¹ ∈ ZM _ (x • γ) := by
        rw [zm_smul]
        exact ⟨u, S5B.uSub_le_zm h.le γ hu, rfl⟩
      exact hWst'' (hgenW x hx hxu)
    have hATx : critA _ (baseA (puAmalgam h.le)) (x⁻¹ • α'') ≤ S59.tZero h.le L γ := by
      have e := S59.critA_smul (puAmalgam h.le) x⁻¹ (baseA (puAmalgam h.le)) α''
      rw [hxα x hx] at e
      rw [e, ← map_conj_eq_of_mem_normalizer (hTn (inv_mem (hKst hx)))]
      exact Subgroup.map_mono hAT
    have h1 := zm_le_centralizer_uSub_inf_qv h hb' hd hβγ hγα hξ hξα hP (hcx x hx) hUx hATx
      (hKH x hx)
    have h2 := map_conj_le_centralizer x h1
    rw [← zm_smul, Subgroup.map_inf _ _ _ (MulAut.conj x).injective, ← S5B.uSub_smul h.le hLn,
      ← qv_smul, smul_inv_smul, (mem_stab _).1 (hKst hx)] at h2
    exact h2
  have hWQα : W ≤ Qv _ (baseA (puAmalgam h.le)) :=
    hWle fun x hx => zm_le_qv_of_dist_lt _ ((isMVtx_smul _ x γ).2 hγ)
      (by rw [SimpleGraph.dist_comm, hdist x hx]; exact hb')
  have hYX : W ≤ Subgroup.centralizer (XM _ (baseA (puAmalgam h.le)) : Set _) :=
    hWQα.trans (qv_le_centralizer_xm _ _)
  have hYR : W ≤ Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α'' : Set _) :=
    hYX.trans (Subgroup.centralizer_le hRX)
  obtain ⟨-, -, -, hHX, -⟩ := S59.hSub_facts h hb' hd hβγ hγα hξ hξα hP
  have hAWX : ⁅critA _ (baseA (puAmalgam h.le)) α'', W⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
    rw [Subgroup.commutator_comm, hWdef]
    refine S59.commutator_iSup_le (fun x => ?_) (fun x => ?_)
    · exact (S59.zm_le_stab_of_dist_le h ((isMVtx_smul _ (x : (puAmalgam h.le).Universal) γ).2 hγ)
        (by rw [SimpleGraph.dist_comm, hdist x x.2]; omega)).trans (stab_le_normalizer_xm _ _)
    · refine (Subgroup.commutator_mono le_rfl hAT).trans ?_
      rw [S59.commutator_zm_tZero_smul h hb' hβγ (hKst x.2)]
      rw [← map_conj_eq_of_mem_normalizer (stab_le_normalizer_xm _ (baseA (puAmalgam h.le))
        (hKst x.2))]
      exact Subgroup.map_mono hHX
  have hWZX : ⁅W, S5.zHat _ (baseA (puAmalgam h.le)) α''⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
    by_cases hY : ⁅ZM (puAmalgam h.le) α'', W⁆ ≤
        ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α''⁆ ⊔
          ⁅critA (puAmalgam h.le) (baseA _) α'', W⁆
    · rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono inf_le_left le_rfl).trans (hY.trans (sup_le hXX hAWX))
    · by_cases hYZ : ⁅W, S5.zHat _ (baseA (puAmalgam h.le)) α''⁆ ≤
          critR _ (baseA (puAmalgam h.le)) α''
      · exact hYZ.trans hRX
      · obtain ⟨-, hXU, -⟩ := S5B.s33ii2_of' hX2 h hd h32' hc'' hWT hYR hYX hY hYZ
        have hXe := S5Q2.xm_eq_uSub_sup_centralizer h hXU hα''M
        have hZc := S5Q2.xm_inf_centralizer_le_stabCenter h
          (S5Q2.zq_le_centralizer_of_two_le h hd hk) hα''M
        set Zc := XM _ α'' ⊓
          Subgroup.centralizer (puTrans h.le L α'' : Set (puAmalgam h.le).Universal) with hZcdef
        have hZcc : ∀ c ∈ Zc, ∀ g ∈ stab _ α'', g * c = c * g := fun c hc g hg =>
          (S510.mem_stabCenter_iff.1 (hZc hc)).2 g hg
        have hUst'' : S5.uSub h.le L α'' ≤ stab _ α'' :=
          (S5B.uSub_le_zm h.le α'').trans ((zm_le_qv_self _ hα''M hb0).trans (qv_le_stab _ _))
        have hUZn : S5.uSub h.le L α'' ≤
            Subgroup.normalizer (Zc : Set (puAmalgam h.le).Universal) := by
          intro u hu
          rw [Subgroup.mem_normalizer_iff]
          intro c
          constructor
          · intro hc
            rw [hZcc c hc u (hUst'' hu), mul_inv_cancel_right]
            exact hc
          · intro hc
            have hc' := hZcc _ hc u (hUst'' hu)
            have e : u * c * u⁻¹ = c := by
              have h3 : u * (u * c * u⁻¹) = u * c := by rw [hc']; group
              exact mul_left_cancel h3
            rw [← e]
            exact hc
        have hαε : (puAmalgam h.le).treeGraph.Adj (baseA _)
            (geo _ (baseA (puAmalgam h.le)) α'' 1) := adj_geo_one _ (by omega)
        have hdε : (puAmalgam h.le).treeGraph.dist α'' (geo _ (baseA (puAmalgam h.le)) α'' 1) <
            critDist (puAmalgam h.le) := by
          rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hdd'']
          omega
        have hZst : ZM _ (baseA (puAmalgam h.le)) ≤ stab _ α'' :=
          S59.zm_le_stab_of_dist_le h hα hdd''.le
        have hAW : ⁅critA _ (baseA (puAmalgam h.le)) α'', W⁆ = ⊥ := by
          rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
          intro y hy
          have hyX : y ∈ XM _ α'' := hy.1
          rw [hXe, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUZn]
            at hyX
          obtain ⟨u, hu, c, hc, rfl⟩ := hyX
          have hcZ : c ∈ Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _) := by
            rw [Subgroup.mem_centralizer_iff]
            intro z hz
            exact hZcc c hc z (hZst hz)
          have hyZ : u * c ∈ Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _) :=
            Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα) hy.2
          have huZ : u ∈ Subgroup.centralizer (ZM _ (baseA (puAmalgam h.le)) : Set _) := by
            have := mul_mem hyZ (inv_mem hcZ)
            simpa using this
          have huQ : u ∈ Qv _ (baseA (puAmalgam h.le)) :=
            le_qv_of_le_centralizer _ hC hα hαε
              (show Subgroup.closure {u} ≤ _ from (Subgroup.closure_le _).2
                (Set.singleton_subset_iff.2
                  ((S5B.uSub_le_zm h.le α'').trans (zm_le_qv_of_dist_lt _ hα''M hdε) hu)))
              ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 huZ))
              (Subgroup.subset_closure rfl)
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          have hwu := Subgroup.mem_centralizer_iff.1 (hW2 hw) u ⟨hu, huQ⟩
          have hwc := hZcc c hc w (hWst'' hw)
          calc w * (u * c) = (w * u) * c := by group
            _ = (u * w) * c := by rw [hwu]
            _ = u * (w * c) := by group
            _ = u * (c * w) := by rw [hwc]
            _ = u * c * w := by group
        exact (S5B.commutator_zHat_le' h hd hc'' hWT hYR hAW).trans (sup_le hXX hRX)
  have hKW : K ≤ Subgroup.normalizer (W : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun k hk => ?_
    conv_lhs => rw [hWdef]
    rw [Subgroup.map_iSup]
    refine iSup_le fun x => ?_
    rw [← zm_smul, smul_smul]
    exact hgenW _ (mul_mem hk x.2)
  have hWst : W ≤ stab _ (baseA (puAmalgam h.le)) := hWQα.trans (qv_le_stab _ _)
  have hPn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer ((W ⊔ XM _ (baseA (puAmalgam h.le)) : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
    rw [← hgen]
    refine sup_le (le_normalizer_sup hKW (hKst.trans (stab_le_normalizer_xm _ _))) ?_
    exact le_normalizer_sup_of_commutator_le (hZ''st.trans (stab_le_normalizer_xm _ _))
      (hWZX.trans le_sup_right)
  obtain ⟨y₀, hy₀Z, hy₀st, hy₀2, hy₀Q⟩ := S59.exists_zHat_not_mem h55 h56 h hmin hb' hd hc''
  have hPy : ∀ w ∈ W ⊔ XM _ (baseA (puAmalgam h.le)),
      y₀ * w * y₀⁻¹ * w⁻¹ ∈ XM _ (baseA (puAmalgam h.le)) := by
    have hz : ⁅W ⊔ XM _ (baseA (puAmalgam h.le)), Subgroup.zpowers y₀⁆ ≤
        XM _ (baseA (puAmalgam h.le)) := by
      refine S5B.commutator_sup_le_of_le (hWst.trans (stab_le_normalizer_xm _ _))
        ((xm_le_qv _ _).trans ((qv_le_stab _ _).trans (stab_le_normalizer_xm _ _))) ?_ ?_
      · exact (Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).2 hy₀Z)).trans hWZX
      · exact commutator_le_left_of_le_normalizer
          ((Subgroup.zpowers_le).2 (stab_le_normalizer_xm _ _ hy₀st))
    intro w hw
    have h1 := hz (Subgroup.commutator_mem_commutator hw (Subgroup.mem_zpowers y₀))
    have e : y₀ * w * y₀⁻¹ * w⁻¹ = ⁅w, y₀⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h1
  have hB := S59.inf_le_bSub_of_elt h h32' hα
    (sup_le hWst ((xm_le_qv _ _).trans (qv_le_stab _ _)))
    ((puTrans_le_stab h.le L _).trans hPn) hy₀st hy₀2 hy₀Q hPy
  have hZγW : ZM _ γ ≤ W := by
    have := hgenW 1 (one_mem K)
    rwa [one_smul] at this
  exact hUγB (le_trans (le_inf ((S5B.uSub_le_zm h.le γ).trans (hZγW.trans le_sup_left))
    ((S5B.uSub_le_zm h.le γ).trans (S5B.zm_le_vv_of_dist hγ hd2.le))) hB)

theorem case1_false (h32 : S32) (hX2 : S33.S33X52) (h53 : S53) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ' : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {ξ : Vtx (puAmalgam h.le)}
    (hξ : IsCritical _ ξ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤ 2 ^ k)
    (hnc : ¬ S59.hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      stabCenter _ (baseA (puAmalgam h.le))) : False := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hyp := h.hyp20
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hdd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ'] at this
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 := dist_geo _ (by omega)
  have hγα : γ ≠ baseA _ := by
    intro he
    rw [he, SimpleGraph.dist_self] at hd2
    exact absurd hd2 (by norm_num)
  obtain ⟨hγ, -, -⟩ := S59.gamma_facts h hβγ hγα
  obtain ⟨hHU, -, -, -, -⟩ := S59.hSub_facts h hb' hd hβγ hγα hξ hξα hP
  have hγα' : (puAmalgam h.le).treeGraph.dist γ (baseA _) < critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, hd2]
    exact hb'
  have hHst : S59.hSub h.le L γ ≤ stab _ (baseA (puAmalgam h.le)) :=
    hHU.trans ((S5B.uSub_le_zm h.le γ).trans ((zm_le_qv_of_dist_lt _ hγ hγα').trans
      (qv_le_stab _ _)))
  obtain ⟨h₁, hh₁, hh₁c⟩ := Set.not_subset.1 hnc
  obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ :=
    S59.exists_mul_of_mem_hSub h53 h hmin hb' hd hβγ hγα hξ hξα hP hh₁
  have hu₁L : u₁ ∉
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    fun hL => hh₁c (mul_mem (S59.uSub_inf_le_stabCenter h hd hα ⟨hu₁, hL⟩) hd₁)
  have hCC : stab _ (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer ({u₁} : Set (puAmalgam h.le).Universal) =
      stab _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer ({u₁ * d₁} : Set (puAmalgam h.le).Universal) := by
    ext g
    constructor
    · rintro ⟨hg, hgu⟩
      refine ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hgd := (S510.mem_stabCenter_iff.1 hd₁).2 g hg
      have hgu' := Subgroup.mem_centralizer_singleton_iff.1 hgu
      calc g * (u₁ * d₁) = g * u₁ * d₁ := by group
        _ = u₁ * g * d₁ := by rw [hgu']
        _ = u₁ * (g * d₁) := by group
        _ = u₁ * (d₁ * g) := by rw [hgd]
        _ = u₁ * d₁ * g := by group
    · rintro ⟨hg, hgh⟩
      refine ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have hgd := (S510.mem_stabCenter_iff.1 hd₁).2 g hg
      have hgh' := Subgroup.mem_centralizer_singleton_iff.1 hgh
      calc g * u₁ = g * (u₁ * d₁) * d₁⁻¹ := by group
        _ = u₁ * d₁ * g * d₁⁻¹ := by rw [hgh']
        _ = u₁ * (d₁ * g) * d₁⁻¹ := by group
        _ = u₁ * (g * d₁) * d₁⁻¹ := by rw [hgd]
        _ = u₁ * g := by group
  set K := stab _ (baseA (puAmalgam h.le)) ⊓
    Subgroup.centralizer ({u₁ * d₁} : Set (puAmalgam h.le).Universal) with hKdef
  obtain ⟨-, -, hZ'st, -, -, -⟩ := S5B.crit_facts h hc
  have hZ'2 : IsPGroup 2 (S5.zHat _ (baseA (puAmalgam h.le)) α') :=
    (isPGroup_qv _ hyp ((isMVtx_iff_of_adj _ (adj_geo_one_of_isCritical _ hb0 hc)).1 hα)).to_le
      (inf_le_left.trans (zm_le_qv_geo_one _ hyp hb0 hc))
  obtain ⟨m, hm, e, he, hne⟩ := S59.exists_conj_not_comm h hd hα hu₁ hu₁L hZ'st hZ'2
    (S59.zHat_not_le_qv_baseA h55 h56 h hmin hb' hd hc)
  have hmα : m⁻¹ • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 (inv_mem hm)
  set α'' := m⁻¹ • α' with hα''def
  have hc'' : IsCritical _ (baseA (puAmalgam h.le)) α'' := by
    have := (isCritical_smul _ m⁻¹ _ _).2 hc
    rwa [hmα] at this
  have hZ'' : S5.zHat _ (baseA (puAmalgam h.le)) α'' =
      (S5.zHat _ (baseA (puAmalgam h.le)) α').map (MulAut.conj m⁻¹).toMonoidHom := by
    have := S5B.zHat_smul _ m⁻¹ (baseA (puAmalgam h.le)) α'
    rwa [hmα] at this
  have he'' : m⁻¹ * e * m ∈ S5.zHat _ (baseA (puAmalgam h.le)) α'' := by
    rw [hZ'']
    exact ⟨e, he, by simp [mul_assoc]⟩
  have hne'' : m⁻¹ * e * m * u₁ ≠ u₁ * (m⁻¹ * e * m) := by
    intro hc'
    apply hne
    calc e * (m * u₁ * m⁻¹) = m * (m⁻¹ * e * m * u₁) * m⁻¹ := by group
      _ = m * (u₁ * (m⁻¹ * e * m)) * m⁻¹ := by rw [hc']
      _ = m * u₁ * m⁻¹ * e := by group
  obtain ⟨-, -, hZ''st, -, -, -⟩ := S5B.crit_facts h hc''
  have hZ''2 : IsPGroup 2 (S5.zHat _ (baseA (puAmalgam h.le)) α'') :=
    (isPGroup_qv _ hyp ((isMVtx_iff_of_adj _ (adj_geo_one_of_isCritical _ hb0 hc'')).1 hα)).to_le
      (inf_le_left.trans (zm_le_qv_geo_one _ hyp hb0 hc''))
  have hgen : K ⊔ S5.zHat _ (baseA (puAmalgam h.le)) α'' = stab _ (baseA (puAmalgam h.le)) := by
    rw [← hCC]
    exact S59.centralizer_sup_eq h hd hα hu₁ hu₁L hZ''st hZ''2 he'' hne''
  have hγ'' : geo _ (baseA (puAmalgam h.le)) α'' 2 = m⁻¹ • γ := by
    have := geo_smul _ m⁻¹ (baseA (puAmalgam h.le)) α' 2
    rw [hmα] at this
    exact this
  have hKH : ∀ x ∈ K, ¬ S59.hSub h.le L γ ≤
      Subgroup.centralizer (ZM _ (x⁻¹ • α'') : Set (puAmalgam h.le).Universal) := by
    intro x hx hle
    have hxh := Subgroup.mem_centralizer_singleton_iff.1 hx.2
    set e'' := m⁻¹ * e * m with he''def
    have he''Z : e'' ∈ ZM _ α'' := (Subgroup.mem_inf.1 he'').1
    have hmem : x⁻¹ * e'' * x ∈ ZM _ (x⁻¹ • α'') := by
      rw [zm_smul]
      exact ⟨e'', he''Z, by simp [mul_assoc]⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (hle hh₁) _ hmem
    have h2 : e'' * (u₁ * d₁) = (u₁ * d₁) * e'' := by
      have e1 : u₁ * d₁ = x * (u₁ * d₁) * x⁻¹ := by
        rw [hxh, mul_inv_cancel_right]
      calc e'' * (u₁ * d₁) = x * ((x⁻¹ * e'' * x) * (u₁ * d₁)) * x⁻¹ := by
            nth_rewrite 1 [e1]
            group
        _ = x * ((u₁ * d₁) * (x⁻¹ * e'' * x)) * x⁻¹ := by rw [hcomm]
        _ = (u₁ * d₁) * e'' := by
            nth_rewrite 2 [e1]
            group
    have hd₁e := (S510.mem_stabCenter_iff.1 hd₁).2 e'' (hZ''st he'')
    apply hne''
    calc e'' * u₁ = e'' * (u₁ * d₁) * d₁⁻¹ := by group
      _ = u₁ * d₁ * e'' * d₁⁻¹ := by rw [h2]
      _ = u₁ * (d₁ * e'') * d₁⁻¹ := by group
      _ = u₁ * (e'' * d₁) * d₁⁻¹ := by rw [hd₁e]
      _ = u₁ * e'' := by group
  exact case1_core h32 hX2 h55 h56 h hmin hb hd hk hβγ hγα hξ hξα hP inf_le_left hc''
    (inv_mem hm) hγ'' hgen hKH

end Case1

end CFSG.Quasithin.MS93.S59R

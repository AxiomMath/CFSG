module

public import CFSG.Quasithin.MS93.S511B6
public import CFSG.Quasithin.MS93.S5B56Z
public import CFSG.Quasithin.MS93.S5Q2EvenZ
public import CFSG.Quasithin.MS93.C56Red

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S511S

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem xm_inf_centralizer_jOff_le (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) :
    XM _ ρ ⊓ Subgroup.centralizer (S5.jOff h.le L (2 ^ k) ρ ε : Set _) ≤
      S5.uSub h.le L ρ ⊔ S5.dSub h.le L ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl, rfl⟩ := exists_smul_base_edge _ hρ hρε
  have key := h53 G M T L h hmin hb k F _ _ a hd
  rw [xm_smul, S5B.jOff_smul h.le hLn, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, S5B.uSub_smul h.le hLn,
    S5B.dSub_smul h.le hLn, ← Subgroup.map_sup]
  exact Subgroup.map_mono key

theorem xm_inf_uSub_sup_dSub_le (h : PUHyp M T L)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) :
    XM _ ρ ⊓ (S5.uSub h.le L ρ ⊔ S5.dSub h.le L ρ) ≤
      S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  rintro x ⟨hxX, hxUD⟩
  have hn : S5.dSub h.le L ρ ≤
      Subgroup.normalizer (S5.uSub h.le L ρ : Set (puAmalgam h.le).Universal) :=
    (inf_le_left.trans (qv_le_stab _ _)).trans
      (le_normalizer_commutator (stab_le_normalizer_zm _ _)
        (stab_le_normalizer_puTrans h.le
          ((Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer) _))
  have hx' : x ∈ ((S5.uSub h.le L ρ ⊔ S5.dSub h.le L ρ : Subgroup _) :
      Set (puAmalgam h.le).Universal) := hxUD
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hn] at hx'
  obtain ⟨u, hu, d, hdD, rfl⟩ := hx'
  have huX : u ∈ XM _ ρ := zm_le_xm _ hyp hb0 hρ (S5B.uSub_le_zm h.le _ hu)
  have hdX : d ∈ XM _ ρ := by
    have e : d = u⁻¹ * (u * d) := by group
    rw [e]
    exact mul_mem (inv_mem huX) hxX
  have hdZ : d ∈ stabCenter _ ρ :=
    S5Q2.xm_inf_centralizer_le_stabCenter h hZc hρ ⟨hdX, hdD.2⟩
  exact mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨hdX, hdZ⟩)

theorem xm_inf_centralizer_jOff_le_sup (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G))
    {ρ ε : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε) :
    XM _ ρ ⊓ Subgroup.centralizer (S5.jOff h.le L (2 ^ k) ρ ε : Set _) ≤
      S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ :=
  fun _ hx => xm_inf_uSub_sup_dSub_le h hZc hρ
    ⟨hx.1, xm_inf_centralizer_jOff_le h53 h hmin hb hd hρ hρε hx⟩

omit [Fintype F] in
theorem zm_le_sup_of_jOff (h : PUHyp M T L) {q : ℕ} {ρ ε : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) (hρε : (puAmalgam h.le).treeGraph.Adj ρ ε)
    (hJ : XM _ ρ ⊓ Subgroup.centralizer (S5.jOff h.le L q ρ ε : Set _) ≤
      S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ) :
    ZM _ ρ ≤ S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  rw [S5B.zm_eq_zh_sup_uSub h hρ hρε]
  refine sup_le ?_ le_sup_left
  intro z hz
  refine hJ ⟨?_, ?_⟩
  · exact zm_le_xm _ hyp hb0 hρ (zh_le_zm _ hρε hz)
  · exact Subgroup.centralizer_le (S5B.jOff_le_qv h.le L _ _ _) (zh_le_centralizer _ _ hz)

theorem zm_le_sup (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G)) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) :
    ZM _ ρ ≤ S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ := by
  obtain ⟨ε, hρε⟩ : ∃ ε, (puAmalgam h.le).treeGraph.Adj ρ ε := by
    obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
    exact ⟨g • baseB _, (adj_smul _ g _ _).2 (adj_baseA_baseB _)⟩
  exact zm_le_sup_of_jOff h hρ hρε (xm_inf_centralizer_jOff_le_sup h53 h hmin hb hd hZc hρ hρε)

theorem zq_le_centralizer_of_not (h32 : S32) (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hn : ¬ (k = 1 ∧ Xq M = Uq M T L ⊔ Zq M L)) : Zq M L ≤ Subgroup.centralizer (M : Set G) := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    exact S5Q2.X52.zq_le_centralizer_of_ne h hd (h32 G M T L h).2.1 fun hXU => hn ⟨rfl, hXU⟩
  · exact S5Q2.zq_le_centralizer_of_two_le h hd hk

theorem zm_le_sup' (h32 : S32) (h53 : S53) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    ZM _ ρ ≤ S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ := by
  by_cases hn : k = 1 ∧ Xq M = Uq M T L ⊔ Zq M L
  · obtain ⟨rfl, hXU⟩ := hn
    exact S5Q2.UC.zm_le_uSub_sup h hd hXU hρ
  · exact zm_le_sup h53 h hmin hb hd (zq_le_centralizer_of_not h32 h hd hn) hρ

theorem zm_inf_xm_inf_centralizer_jOff_le_zm_e (h32 : S32) (h53 : S53) (hZ : S5Q2.Q2EvenZ)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) :
    ZM _ δ ⊓ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) ≤
      ZM _ (baseA (puAmalgam h.le)) := by
  by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
  · exact S5Q2.UC.zm_inf_xm_inf_centralizer_jOff_le_zm h hZ hmin hb hd hXU hβδ hl
  · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
      ((xm_inf_centralizer_jOff_le_sup h53 h hmin hb hd
        (zq_le_centralizer_of_not h32 h hd fun hn => hXU hn.2) (isMVtx_baseA _)
        (adj_baseA_baseB _)).trans (uSub_sup_le_zm h (isMVtx_baseA _)))

theorem zm_inf_xm_inf_centralizer_jOff_le_zm_e' (h32 : S32) (h53 : S53) (hZ : S5Q2.Q2EvenZ)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {δ : Vtx (puAmalgam h.le)}
    (hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a δ l) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ XM _ δ ⊓
        Subgroup.centralizer (S5.jOff h.le L (2 ^ k) δ (baseB _) : Set _) ≤ ZM _ δ := by
  have hδM : IsMVtx _ δ := (isMVtx_iff_of_adj _ hβδ.symm).2 (not_isMVtx_baseB _)
  by_cases hXU : Xq M = Uq M T L ⊔ Zq M L
  · exact S5Q2.UC.zm_inf_xm_inf_centralizer_jOff_le_zm' h hZ hmin hb hd hXU hβδ hl
  · exact (le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
      ((xm_inf_centralizer_jOff_le_sup h53 h hmin hb hd
        (zq_le_centralizer_of_not h32 h hd fun hn => hXU hn.2) hδM hβδ.symm).trans
          (uSub_sup_le_zm h hδM))

theorem critR_le_zm_gp_of' (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a)
    (h56 : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hJZ : ∀ (δ : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F)),
      (puAmalgam h.le).treeGraph.Adj (baseB _) δ → S5.Case56 h (2 ^ k) a δ l →
      ZM _ (baseA (puAmalgam h.le)) ⊓ XM _ δ ⊓
        Subgroup.centralizer (S5.jOff h.le L (2 ^ k) δ (baseB _) : Set _) ≤ ZM _ δ)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    critR _ γ γ' ≤ ZM _ (geo _ γ γ' 2) := by
  obtain ⟨g, rfl, -, hc', hβ'⟩ := S510.exists_base_crit h hc
  obtain ⟨l, hl⟩ := h56 _ hc' hβ'
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) (g⁻¹ • γ') = critDist (puAmalgam h.le) :=
    hc'.2.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB (puAmalgam h.le))
      (geo _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := g⁻¹ • γ') (i := 1) (by omega)
    rwa [hβ'] at this
  have key : critR _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') ≤
      ZM _ (geo _ (baseA (puAmalgam h.le)) (g⁻¹ • γ') 2) :=
    (le_inf (le_inf (commutator_le_left_of_le_normalizer ((zm_le_stab_of_isCritical _ h.hyp20
      h.critDist_pos hc').trans (stab_le_normalizer_zm _ _)))
        (S511.critR_le_xm_baseA h hb hd hc' hβ' hl))
      (critR_le_centralizer_jOff_baseA h hb hd hc' hβ' hl)).trans (hJZ _ _ hβγ hl)
  have e1 : γ' = g • (g⁻¹ • γ') := (smul_inv_smul g γ').symm
  rw [e1, S510.critR_smul, geo_smul, zm_smul, map_conj_le_map_conj_iff]
  exact key

theorem critR_le_zm_gp (h32 : S32) (h53 : S53) (hZ : S5Q2.Q2EvenZ) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (h56 : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    critR _ γ γ' ≤ ZM _ (geo _ γ γ' 2) :=
  critR_le_zm_gp_of' h hb hd h56
    (fun _ _ hβδ hl => zm_inf_xm_inf_centralizer_jOff_le_zm_e' h32 h53 hZ h hmin hb hd hβδ hl) hc

theorem zz56 (h53 : S53) (h54 : S54) (h59 : S5B.S59) (h32 : S32) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have h59' := h59 G M T L h hmin hb k F _ _ a hd α' hc hαβ
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγ
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hγM : IsMVtx _ γ := (isMVtx_iff_of_adj _ hβγ.symm).2 (not_isMVtx_baseB _)
  have hdαγ : (puAmalgam h.le).treeGraph.dist (baseA _) γ = 2 := dist_geo _ (by omega)
  obtain ⟨hJγ, hl', -, hJl⟩ := hl
  have hcardJ := S5C56.lt_card_vIm_jOff h54 h hmin hb2 hd hl' hJl
  have hUJ := S5B.uSub_inf_centralizer_le_baseA h hd hl' hJl hcardJ
  have hcen : ∀ c ∈ stabCenter _ (baseA (puAmalgam h.le)), ∀ K : Subgroup _,
      K ≤ stab _ (baseA (puAmalgam h.le)) → c ∈ Subgroup.centralizer (K : Set _) :=
    fun c hc' K hK => Subgroup.mem_centralizer_iff.2 fun y hy =>
      S510.commute_of_mem_stabCenter hc' (hK hy)
  have hJβ : S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤
      stab _ (baseA (puAmalgam h.le)) :=
    (S5B.jOff_le_qv h.le L _ _ _).trans (qv_le_stab_of_adj _ hαβadj.symm)
  have hQ₁st : S5.vPre h.le a (MSP.qLine l) ≤ stab _ (baseA (puAmalgam h.le)) := by
    rw [S5B.vPre_eq_imM h.le, puAmalgam.stab_baseA]
    exact imM_mono h.le (Subgroup.map_subtype_le _)
  have hdec : ∀ z ∈ ZM _ (baseA (puAmalgam h.le)),
      ∃ u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)),
        ∃ c ∈ stabCenter _ (baseA (puAmalgam h.le)), u * c = z := by
    intro z hz
    obtain ⟨u, hu, c, hc', e⟩ := S510.exists_mul_of_mem_sup h
      (zm_le_sup' h32 h53 h hmin hb2 hd hα hz)
    exact ⟨u, hu, c, hc', e.symm⟩
  by_contra hne
  obtain ⟨w, hw, hwQ⟩ := Set.not_subset.1 hne
  have hwJ : w ∉ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) := by
    intro hwJ
    apply hwQ
    obtain ⟨u, hu, c, hc', rfl⟩ := hdec w hw.1
    have hcJ := hcen c hc' _ hJβ
    have huJ : u ∈ Subgroup.centralizer
        (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) := by
      have e : u = u * c * c⁻¹ := by group
      rw [e]
      exact mul_mem hwJ (inv_mem hcJ)
    exact mul_mem (hUJ ⟨hu, huJ⟩) (hcen c hc' _ hQ₁st)
  obtain ⟨t, ht, htα⟩ := exists_mem_stab_smul _ hαβadj.symm hβγ
  have htβ : t • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 ht
  have htβ' : t⁻¹ • baseB (puAmalgam h.le) = baseB _ := (mem_stab _).1 (inv_mem ht)
  have htJ : (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) := by
    have e := S5B.jOff_smul h.le hLn (2 ^ k) t (baseA (puAmalgam h.le)) (baseB _)
    rw [htα, htβ, hJγ] at e
    exact e.symm
  have htJ' : (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
      (MulAut.conj t⁻¹).toMonoidHom = S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) := by
    calc _ = ((S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)).map
          (MulAut.conj t).toMonoidHom).map (MulAut.conj t⁻¹).toMonoidHom := by rw [htJ]
      _ = _ := map_conj_inv_map_conj _ t
  set δ := t⁻¹ • baseA (puAmalgam h.le) with hδ
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := (adj_smul _ t⁻¹ _ _).2 hαβadj.symm
    rwa [htβ'] at this
  have hδM : IsMVtx _ δ := (isMVtx_smul _ _ _).2 hα
  have hQδJ : Qv _ δ ≤ S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) := by
    have e := S5B.jOff_smul h.le hLn (2 ^ k) t⁻¹ (baseA (puAmalgam h.le)) (baseB _)
    rw [htJ', htβ'] at e
    exact (S5B.qv_le_jOff h Nat.one_le_two_pow hδM hβδ.symm).trans e.le
  have hZγ : ZM _ γ = (ZM _ (baseA (puAmalgam h.le))).map (MulAut.conj t).toMonoidHom := by
    rw [← htα, zm_smul]
  have hZα : ZM _ (baseA (puAmalgam h.le)) = (ZM _ δ).map (MulAut.conj t).toMonoidHom := by
    rw [← zm_smul, hδ, smul_inv_smul]
  have hw₀α : t⁻¹ * w * t ∈ ZM _ (baseA (puAmalgam h.le)) := by
    have h1 : w ∈ ZM _ γ := hw.2
    rw [hZγ, mem_map_conj] at h1
    exact h1
  have hw₀δ : t⁻¹ * w * t ∈ ZM _ δ := by
    have h1 : w ∈ ZM _ (baseA (puAmalgam h.le)) := hw.1
    rw [hZα, mem_map_conj] at h1
    exact h1
  have hCJ : (Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _)).map
        (MulAut.conj t).toMonoidHom =
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) := by
    rw [← PU.centralizer_map_mulEquiv, htJ]
  have hw₀J : t⁻¹ * w * t ∉ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) := fun h0 =>
    hwJ (by rw [← hCJ, mem_map_conj]; exact h0)
  obtain ⟨u₀, hu₀, c₀, hc₀, he₀⟩ := hdec _ hw₀α
  have hu₀J : u₀ ∉ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) := fun h0 =>
    hw₀J (by rw [← he₀]; exact mul_mem h0 (hcen c₀ hc₀ _ hJβ))
  have hu₀δ : u₀ ∈ Subgroup.centralizer (Qv _ δ : Set (puAmalgam h.le).Universal) := by
    have e : u₀ = t⁻¹ * w * t * c₀⁻¹ := by rw [← he₀]; group
    rw [e]
    exact mul_mem (zm_le_centralizer_qv _ hyp hδM hw₀δ)
      (inv_mem (hcen c₀ hc₀ _ (hQδJ.trans hJβ)))
  have hn : ¬ S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (Qv _ δ : Set _) ≤
        Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set _) := fun hle =>
    hu₀J (Subgroup.centralizer_le hJl (hle ⟨hu₀, hu₀δ⟩))
  have hrel := S5C56.relIndex_centralizer_le_of_not_le h hd hl' (hQδJ.trans hJl) hn
  have hUγ : S5.uSub h.le L γ =
      (S5.uSub h.le L (baseA (puAmalgam h.le))).map (MulAut.conj t).toMonoidHom := by
    rw [← htα, S5B.uSub_smul h.le hLn]
  have hQα : Qv _ (baseA (puAmalgam h.le)) = (Qv _ δ).map (MulAut.conj t).toMonoidHom := by
    rw [← qv_smul, hδ, smul_inv_smul]
  have hrel' : (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _)).relIndex
      (S5.uSub h.le L γ) ≤ 2 ^ k := by
    rw [hUγ, hQα, PU.centralizer_map_mulEquiv,
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj t).injective]
    exact hrel
  have hUγZ : S5.uSub h.le L γ ≤ ZM _ γ :=
    commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans
      (stab_le_normalizer_zm _ _))
  have hUγQ : S5.uSub h.le L γ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    hUγZ.trans (zm_le_qv_of_dist_lt _ hγM (by
      rw [tdist_comm, hγ, dist_geo _ (by omega)]
      omega))
  have hXL := S5C56.commutator_xm_puTrans_le_uSub h32 h
  have hUαZ : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ ZM _ (baseA (puAmalgam h.le)) :=
    commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L _).trans
      (stab_le_normalizer_zm _ _))
  have hCB : Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _) ⊓ S5.uSub h.le L γ ≤
      S5.bSub h.le L (baseA (puAmalgam h.le)) ⊓ S5.uSub h.le L γ := by
    rintro u ⟨huC, huU⟩
    have huX : u ∈ XM _ (baseA (puAmalgam h.le)) :=
      mem_omegaOneCenterOf (hUγQ huU) (fun y hy => Subgroup.mem_centralizer_iff.1 huC y hy)
        (sq_eq_one_of_mem_omegaOneCenterOf (zm_le_xm _ hyp hb0 hγM (hUγZ huU)))
    refine ⟨Subgroup.subset_closure ⟨?_, fun y hy => ?_⟩, huU⟩
    · exact le_iSup₂_of_le (f := fun ρ' (_ : ρ' ∈ {ρ' : Vtx (puAmalgam h.le) |
        (puAmalgam h.le).treeGraph.dist (baseA (puAmalgam h.le)) ρ' ≤ 2}) =>
          Zv (puAmalgam h.le) ρ') γ hdαγ.le (zv_of_isMVtx _ hγM).ge (hUγZ huU)
    · exact hUαZ (hXL (Subgroup.commutator_mem_commutator huX hy))
  have hUγβ : S5.uSub h.le L γ ≤ Qv _ (baseB (puAmalgam h.le)) :=
    hUγZ.trans ((zm_le_qv_self _ hγM hb0).trans (qv_le_qv _ hyp hγM hβγ.symm))
  have : Finite ↥(Qv (puAmalgam h.le) (baseB (puAmalgam h.le))) :=
    finite_qv _ hyp (not_isMVtx_baseB _)
  have : Finite ↥(S5.uSub h.le L γ) :=
    Finite.of_injective (Subgroup.inclusion hUγβ) (Subgroup.inclusion_injective hUγβ)
  have hle : (S5.bSub h.le L (baseA (puAmalgam h.le))).relIndex (S5.uSub h.le L γ) ≤
      (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) : Set _)).relIndex
        (S5.uSub h.le L γ) := by
    rw [← Subgroup.inf_relIndex_right (S5.bSub h.le L (baseA (puAmalgam h.le))),
      ← Subgroup.inf_relIndex_right (Subgroup.centralizer (Qv _ (baseA (puAmalgam h.le)) :
        Set (puAmalgam h.le).Universal))]
    exact Subgroup.relIndex_le_of_le_left hCB
      (by rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
  omega

theorem c56x_opp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hZ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hopp : S5.Opp56 h (2 ^ k) a l g x) :
    ZM _ (x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
        ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  intro z hz
  have h1 := hZ ⟨hz.1.2, hz.2⟩
  have hzμ : z ∈ ZM _ ((g * x)⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) := by
    rw [mul_inv_rev, mul_smul]
    exact hz.1.1
  have h2 := S5C56.zm_inf_zm_smul_le h hZ (inv_mem hgx) ⟨hz.1.2, hzμ⟩
  rw [inv_inv] at h2
  refine S5C56.le_stabCenter_of_gen h hd hl (g := g * x) (fun E hE hE2 hErel => ?_)
    ⟨⟨hz.1.2, h1⟩, h2⟩
  exact hopp (S5.rconj (g * x) E) E (hE2.map _) hE2
    ((S5B.rconj_le_rconj_iff (g := g * x)).2 hE) hE
    (by rw [S5C56.relIndex_rconj h hgx]; exact hErel) hErel

omit [Fintype F] in
abbrev GoodLamF (h : PUHyp M T L) (q : ℕ) (a : ↥M →* ↥(StatedSp 2 F))
    (α' μ : Vtx (puAmalgam h.le)) : Prop :=
  ∃ (l : Submodule F (MSP.V4 F)) (g x : (puAmalgam h.le).Universal),
    S5.Case56 h q a (geo _ (baseA (puAmalgam h.le)) α' 2) l ∧
    g ∈ stab _ (baseA (puAmalgam h.le)) ∧ x ∈ puTrans h.le L (baseA _) ∧
    S5.Concl56f h q a α' l g x ∧
    (μ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
      μ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∧
        ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ≤
          Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2))

theorem exists_goodF (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54) (h56f : S5.S56f)
    (h59 : S5B.S59) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {l : Submodule F (MSP.V4 F)}
    (hl : S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) :
    ∃ μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2),
      ¬ ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) ∧ GoodLamF h (2 ^ k) a α' μ := by
  have hd2 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hβγ : (puAmalgam h.le).treeGraph.Adj (baseB (puAmalgam h.le))
      (geo _ (baseA (puAmalgam h.le)) α' 2) := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  obtain ⟨g, hg, x, hx, hconc⟩ :=
    h56f G M T L h hmin (by omega) k F _ _ a hd α' hc hαβ l hl.2.1 hl.2.2.1 hl.2.2.2
  by_cases hZ : ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)
  · have hZx : ¬ ZM _ (x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ≤
        Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) := by
      intro hZx
      have h1 := S5B.s57_case56 h32 hX2 h52 h54 h hmin (by omega) hd hc
        hβγ hl hg hx hconc.1.1 hZ hZx
      have h2 := h59 G M T L h hmin hb k F _ _ a hd α' hc hαβ
      omega
    exact ⟨_, ⟨g, x, hg, hx, Or.inr ⟨l, hl, hconc.1.1⟩, Or.inr rfl⟩, hZx,
      l, g, x, hl, hg, hx, hconc, Or.inr ⟨rfl, hZ⟩⟩
  · exact ⟨_, ⟨g, x, hg, hx, Or.inr ⟨l, hl, hconc.1.1⟩, Or.inl rfl⟩, hZ,
      l, g, x, hl, hg, hx, hconc, Or.inl rfl⟩

theorem cent_of_goodF (h53 : S53) (h54 : S54) (h59 : S5B.S59) (h32 : S32) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {μ : Vtx (puAmalgam h.le)}
    (hgood : GoodLamF h (2 ^ k) a α' μ) :
    ZM _ μ ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  obtain ⟨l, g, x, hl, hg, hx, hconc, rfl | ⟨rfl, -⟩⟩ := hgood
  · exact S5C56.c56g_at h hd hl.2.1 (zz56 h53 h54 h59 h32 h hmin hb hd hc hαβ hl) hg hconc.1.1
  · exact c56x_opp h hd hl.2.1 (zz56 h53 h54 h59 h32 h hmin hb hd hc hαβ hl) hg hx hconc.2

theorem exists_isChain_goodF (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h56f : S5.S56f) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {α α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ α α') (N : ℕ) :
    ∃ s, geo _ s α' (2 * N) = α ∧ S510.IsChain h (2 ^ k) a s α' N ∧
      ∀ j, 1 ≤ j → j ≤ N → ∃ g : (puAmalgam h.le).Universal,
        geo _ s α' (2 * j) = g • baseA (puAmalgam h.le) ∧ geo _ s α' (2 * j + 1) = g • baseB _ ∧
        GoodLamF h (2 ^ k) a (g⁻¹ • geo _ s α' (2 * j + critDist (puAmalgam h.le)))
          (g⁻¹ • geo _ s α' (2 * j - 2)) := by
  obtain ⟨s, hsd, hsα, hcrit, hrest⟩ := S510.exists_chain_sel h hb (GoodLamF h (2 ^ k) a)
    (fun α' hc' hβ' => by
      obtain ⟨l, hl⟩ := h56all α' hc' hβ'
      exact exists_goodF h32 hX2 h52 h54 h56f h59 h hmin hb hd hc' hβ' hl) hc N
  refine ⟨s, hsα, ⟨hsd, hcrit, fun j h1 h2 => (hrest j h1 h2).1, fun j h1 h2 => ?_⟩,
    fun j h1 h2 => ?_⟩
  · obtain ⟨g, h3, h4, h5, -⟩ := (hrest j h1 h2).2
    exact ⟨g, h3, h4, h5⟩
  · obtain ⟨g, h3, h4, -, h6⟩ := (hrest j h1 h2).2
    exact ⟨g, h3, h4, h6⟩

theorem false_of_b6 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h53 : S53) (h54 : S54)
    (h56f : S5.S56f) (hZ : S5Q2.Q2EvenZ) (h59 : S5B.S59) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hd : S5.IsSp4Data M T L k F a) (hb6 : critDist (puAmalgam h.le) = 6)
    (h56all : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ →
      ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) :
    False := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC' := h.centHyp
  have hb : 4 < critDist (puAmalgam h.le) := by omega
  have hcent : ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
      geo _ (baseA _) α' 1 = baseB _ → ∀ μ, GoodLamF h (2 ^ k) a α' μ →
        ¬ ZM _ μ ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2) →
        ZM _ μ ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
          stabCenter _ (baseA (puAmalgam h.le)) := fun α' hc hαβ _ hgood _ =>
    cent_of_goodF h53 h54 h59 h32 h hmin hb hd hc hαβ hgood
  obtain ⟨α', hcα⟩ := exists_isCritical_of_isMVtx _ hyp (isMVtx_baseA (puAmalgam h.le))
  obtain ⟨s, -, hch, hgood⟩ := exists_isChain_goodF h32 hX2 h52 h54 h56f h59 h hmin hb hd
    h56all hcα 2
  have hdd := hch.dist_eq
  have hcr := hch.crit 0 (by omega)
  rw [Nat.mul_zero, zero_add, hb6] at hcr
  set P := geo _ s α' with hP
  set R := critR _ (P 0) (P 6) with hR
  have hR2 : R ≤ ZM _ (P 2) := by
    have := critR_le_zm_gp h32 h53 hZ h hmin (by omega) hd h56all hcr
    rwa [hch.geo_eq (by omega) (by omega) (by omega)] at this
  have hcr' := ms22_iii _ hyp hb0 hC' hcr
  have hR4 : R ≤ ZM _ (P 4) := by
    have := critR_le_zm_gp h32 h53 hZ h hmin (by omega) hd h56all hcr'
    rw [hch.geo_eq' (by omega) (by omega) (by omega)] at this
    rw [hR, critR, Subgroup.commutator_comm]
    exact this
  have hR0 : R ≤ ZM _ (P 0) :=
    commutator_le_left_of_le_normalizer
      ((zm_le_stab_of_isCritical _ hyp hb0 hcr).trans (stab_le_normalizer_zm _ _))
  have hR6 : R ≤ ZM _ (P 6) := by
    rw [hR, critR, Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer
      ((zm_le_stab_of_isCritical _ hyp hb0 hcr').trans (stab_le_normalizer_zm _ _))
  have hZ2 := S511.IsChain.cent_at hch hcent (j := 1) le_rfl (by omega)
    (hgood 1 le_rfl (by omega))
  have hZ4 := S511.IsChain.cent_at hch hcent (j := 2) (by omega) le_rfl
    (hgood 2 (by omega) le_rfl)
  have hRZ2 : R ≤ stabCenter _ (P 2) := (le_inf (le_inf hR0 hR2) hR4).trans hZ2
  have hRZ4 : R ≤ stabCenter _ (P 4) := (le_inf (le_inf hR2 hR4) hR6).trans hZ4
  have hRZ0 : R ≤ stabCenter _ (P 0) := fun r hr =>
    hch.mem_stabCenter_all (i := 1) (by omega) (hRZ2 hr) (hRZ4 hr) 0 (by omega)
  exact S511.critR_not_le_stabCenter h hd hcr hRZ0

end S511S

end CFSG.Quasithin.MS93

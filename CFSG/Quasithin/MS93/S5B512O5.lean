module

public import CFSG.Quasithin.MS93.S5B512JF
public import CFSG.Quasithin.MS93.S5B512
public import CFSG.Quasithin.MS93.S510Loc
public import CFSG.Quasithin.MS93.S510Tv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5B

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Vertex

theorem stab_le_normalizer_uSub_at (h : PUHyp M T L) (ρ : Vtx (puAmalgam h.le)) :
    stab _ ρ ≤ Subgroup.normalizer (S5.uSub h.le L ρ : Set (puAmalgam h.le).Universal) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  exact le_normalizer_commutator (stab_le_normalizer_zm _ _)
    (stab_le_normalizer_puTrans h.le hLn ρ)

theorem lift_at (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {m u : (puAmalgam h.le).Universal}
    (hm : m ∈ stab _ ρ) (hu : u ∈ S5.uSub h.le L ρ)
    (hc : m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer
      (puTrans h.le L ρ : Set (puAmalgam h.le).Universal)) :
    m * u * m⁻¹ = u := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  rw [mem_stab_smul] at hm
  rw [uSub_smul h.le hLn, PU.mem_map_conj] at hu
  rw [puTrans_smul h.le hLn, PU.centralizer_map_mulEquiv, PU.mem_map_conj] at hc
  have e : g⁻¹ * (m * u * m⁻¹ * u⁻¹) * g =
      (g⁻¹ * m * g) * (g⁻¹ * u * g) * (g⁻¹ * m * g)⁻¹ * (g⁻¹ * u * g)⁻¹ := by group
  rw [e] at hc
  set m' := g⁻¹ * m * g with hm'
  set u' := g⁻¹ * u * g with hu'
  have key : m' * u' * m'⁻¹ = u' := by
    rw [puAmalgam.stab_baseA] at hm
    rw [uSub_baseA h] at hu
    rw [puTrans_L_baseA h] at hc
    obtain ⟨m₀, -, hm₀⟩ := hm
    obtain ⟨u₀, hu₀, hu₀e⟩ := hu
    rw [← hm₀, ← hu₀e] at hc ⊢
    have hu₀' : (u₀ : G) ∈ Uq M T L := Subgroup.mem_subgroupOf.1 hu₀
    have hcL : (m₀ : G) * u₀ * (m₀ : G)⁻¹ * (u₀ : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hlA : (puAmalgam h.le).ofA ⟨l, h.L_le hl⟩ ∈ imM h.le L :=
        ⟨⟨l, h.L_le hl⟩, Subgroup.mem_subgroupOf.2 hl, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hc _ hlA
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul] at h1
      have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
      simpa using h2
    have h3 := hlift m₀ m₀.2 u₀ hu₀' hcL
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using h3)
  calc m * u * m⁻¹ = g * (m' * u' * m'⁻¹) * g⁻¹ := by rw [hm', hu']; group
    _ = g * u' * g⁻¹ := by rw [key]
    _ = u := by rw [hu']; group

theorem stabCenter_inf_xm_le_zh (h : PUHyp M T L) {ρ w : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) (hρw : (puAmalgam h.le).treeGraph.Adj ρ w) :
    stabCenter _ ρ ⊓ XM _ ρ ≤ ZH _ w := by
  intro x ⟨hxZ, hxX⟩
  have hxQ : x ∈ Qv _ w := qv_le_qv _ h.hyp20 hρ hρw (xm_le_qv _ ρ hxX)
  have hxC : x ∈ Subgroup.centralizer (Qv _ w : Set (puAmalgam h.le).Universal) :=
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (S510.commute_of_mem_stabCenter hxZ (qv_le_stab_of_adj _ hρw.symm hy))
  have hx2 : x ^ 2 = 1 := (isElemAbelian_xm _ ρ).2 x hxX
  exact Subgroup.subset_closure ⟨⟨hxQ, hxC⟩, hx2⟩

end Vertex

section S33

theorem s512_s33 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h : PUHyp M T L)
    (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hδ2 : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ α' (baseA (puAmalgam h.le)) 2) = 2)
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    (hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2)
    (hn : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ ⊓ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)) :
    (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k ∧
      Xq M = Uq M T L ⊔ Zq M L ∧
      Nat.card ↥⁅S5.uSub h.le L μ ⊓ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2),
        critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k ∧
      ⁅S5.uSub h.le L μ ⊓ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2),
          critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
        critR _ (baseA (puAmalgam h.le)) α' ⊔ stabCenter _ α' := by
  have hyp := h.hyp20
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  obtain ⟨-, -, hZhst, hRX, hXX, hQQ⟩ := crit_facts h hc
  obtain ⟨hZQ, hZR⟩ := zm_le_centralizer_critR h hb hc hμ hdμ
  set δ := geo _ α' (baseA (puAmalgam h.le)) 2 with hδ
  set Y := S5.uSub h.le L μ ⊓ Qv _ δ with hY
  have hYZ : Y ≤ ZM _ μ := inf_le_left.trans (uSub_le_zm h.le μ)
  have hZhX : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.normalizer (XM _ (baseA (puAmalgam h.le)) : Set _) :=
    hZhst.trans (stab_le_normalizer_xm _ _)
  have hAQ : critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ (baseA (puAmalgam h.le)) := inf_le_right
  have hQY : Qv _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (Y : Set _) := by
    have h1 : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ μ :=
      qv_le_stab_of_dist_le_two _ hyp hα hdμ.le
    have h2 : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ δ :=
      qv_le_stab_of_dist_le_two _ hyp hα hδ2.le
    exact (le_inf (h1.trans (stab_le_normalizer_uSub_at h μ))
      (h2.trans (stab_le_normalizer_qv _ _))).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hAY : ⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆ ≤ Y := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (hAQ.trans hQY)
  have hY3 : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆ := by
    intro hle
    apply hn
    refine le_normalizer_sup_of_commutator_le hZhX ?_
    rw [Subgroup.commutator_comm]
    refine ((Subgroup.commutator_mono inf_le_left le_rfl).trans hle).trans
      (sup_le (hXX.trans le_sup_right) (hAY.trans le_sup_left))
  have hYZ' : ¬ ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
      critR _ (baseA (puAmalgam h.le)) α' := by
    intro hle
    exact hn (le_normalizer_sup_of_commutator_le hZhX (hle.trans (hRX.trans le_sup_right)))
  obtain ⟨h1, h3, h4⟩ := s33ii2_of' hX2 h hd (h32 G M T L h).2.1 hc (inf_le_right.trans hQQ)
    (hYZ.trans hZR) ((hYZ.trans hZQ).trans (qv_le_centralizer_xm _ _)) hY3 hYZ'
  refine ⟨h1, h3, h4 ?_⟩
  have h52iii := (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.2
  have hle : Y ≤ Vv _ (baseA (puAmalgam h.le)) ⊓ Qv _ δ :=
    le_inf (hYZ.trans (zm_le_vv_of_dist hμ hdμ.le)) inf_le_right
  refine le_bot_iff.1 ?_
  rw [← h52iii]
  exact Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl hle) hle

end S33

section CritR

theorem critR_le_commutator_uSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    critR _ (baseA (puAmalgam h.le)) α' ≤ ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), ZM _ α'⁆ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) := hc.2.1
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  have hZ'T : ZM _ α' ≤ Qv _ (baseB (puAmalgam h.le)) := by
    refine zm_le_qv_of_dist_lt _ hα' ?_
    rw [← hαβ, SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd]
    omega
  have hcr := ms22_iii _ hyp hb0 h.centHyp hc
  have hd' : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) :=
    hcr.2.1
  have h1 : (puAmalgam h.le).treeGraph.Adj α' (geo _ α' (baseA (puAmalgam h.le)) 1) :=
    adj_geo_one _ (by omega)
  have hda₁ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ α' (baseA (puAmalgam h.le)) 1) <
      critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd']
    omega
  have hZn' : ZM _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (ZM _ α' : Set _) :=
    (zm_le_qv_of_dist_lt _ hα hda₁).trans ((qv_le_stab_of_adj _ h1.symm).trans
      (stab_le_normalizer_zm _ _))
  have hZnU : ZM _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.uSub h.le L (baseA (puAmalgam h.le)) : Set _) :=
    (zm_le_qv_self _ hα hb0).trans ((qv_le_stab _ _).trans (stab_le_normalizer_uSub_at h _))
  have hN := le_normalizer_commutator hZnU hZn'
  rw [critR, zm_eq_zh_sup_uSub h hα hαβadj]
  refine commutator_sup_le_of_le ((zh_le_zm _ hαβadj).trans hN)
    ((uSub_le_zm h.le _).trans hN) ?_ le_rfl
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2
    ((zh_le_centralizer _ _).trans (Subgroup.centralizer_le hZ'T))]
  exact bot_le

theorem commutator_le_centralizer_jOff_of_relIndex_baseA (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {A : Subgroup (puAmalgam h.le).Universal} (hA : A ≤ Qv _ (baseB (puAmalgam h.le)))
    (hrel : (Subgroup.centralizer (A : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le))) = 2 ^ k) :
    ⁅S5.uSub h.le L (baseA (puAmalgam h.le)), A⁆ ≤
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set _) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  rw [puAmalgam.qv_baseB] at hA
  obtain ⟨A₀, hA₀T, hA₀M, rfl⟩ := S5B.exists_eq_imM h.le hA
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  rw [uSub_baseA h, relIndex_centralizer_imM h.le hUM hA₀M] at hrel
  rw [uSub_baseA h, ← imM_commutator h.le hUM hA₀M]
  obtain ⟨p, hp, hcomm, hfix, hxp⟩ := S510.exists_point_of_relIndex h hd hA₀M hrel
  have hAb1 : (A₀.subgroupOf M).map a ≠ ⊥ := by
    intro hbot
    have htop : MSP.fixSp ((A₀.subgroupOf M).map a) = ⊤ := by
      rw [hbot]
      ext v
      simp [MSP.mem_fixSp, MSP.mat_one]
    rw [htop] at hfix
    have h4 : Module.finrank F (MSP.V4 F) = 4 := by simp
    have h3 := MSP.finrank_perp p
    rw [← hfix, finrank_top, h4] at h3
    have hp1 : Module.finrank F p = 1 := hp
    omega
  obtain ⟨g, hgA, hg1⟩ := exists_ne_one_of_ne_bot hAb1
  have hAT : ∀ x ∈ (A₀.subgroupOf M).map a, x ∈ (T.subgroupOf M).map a := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨m, Subgroup.mem_subgroupOf.2 (hA₀T (Subgroup.mem_subgroupOf.1 hm)), rfl⟩
  have hvec : ∀ y (hy : y ∈ Uq M T L), ∀ m (hm : m ∈ A₀),
      MSP.mat (a ⟨m, hA₀M hm⟩) *ᵥ c.vec ⟨y, hy⟩ - c.vec ⟨y, hy⟩ ∈ p := fun y hy m hm => by
    have hmA : a ⟨m, hA₀M hm⟩ ∈ (A₀.subgroupOf M).map a :=
      ⟨⟨m, hA₀M hm⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
    rw [← hcomm]
    exact MSP.sub_mem_commSp hmA _
  suffices hJ : ∃ J₀ : Subgroup G, J₀ ≤ M ∧
      S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ imM h.le J₀ ∧
      (J₀.subgroupOf M).map a ≤ MSP.fixer p by
    obtain ⟨J₀, hJ₀M, hJJ, hJp⟩ := hJ
    exact imM_le_centralizer h.le hJ₀M
      (commutator_le_centralizer_of_vec h hlift c le_rfl hA₀M hvec hJ₀M hJp) hJJ
  rcases h54 G M T L h hmin hb k F _ _ a hd with
    ⟨-, ⟨l, hl, hTl, hJl⟩, -⟩ | ⟨-, hJT, p₀, hp₀, hTq⟩
  · have hpl := le_of_mem_xPoint_stab hp hl (hxp hgA)
      (map_T_le_of_qv_le_vPre h hTl (hAT g hgA)) hg1
    obtain ⟨hJ1, hJ2⟩ := le_imM_of_le_vPre h hJl
    exact ⟨_, Subgroup.map_subtype_le _, hJ1, hJ2.trans (MSP.fixer_antitone hpl)⟩
  · have hTq' : (T.subgroupOf M).map a = MSP.qPoint p₀ := by
      rw [← hTq, vIm_qv_baseB h]
    have hpp : p = p₀ := eq_of_mem_xPoint_qPoint hp hp₀ (hxp hgA) (hTq' ▸ hAT g hgA) hg1
    refine ⟨T, h.le, ?_, ?_⟩
    · rw [hJT, puAmalgam.qv_baseB]
    · rw [hTq', ← hpp]
      exact MSP.qPoint_le_fixer p

end CritR

section JFix

theorem commutator_le_centralizer_jOff_mu (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb4 : critDist (puAmalgam h.le) = 4) (hd : S5.IsSp4Data M T L k F a) (h54 : S54)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {μ ν : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) (hαν : (puAmalgam h.le).treeGraph.Adj (baseA _) ν)
    (hνμ : (puAmalgam h.le).treeGraph.Adj ν μ)
    (hcard : Nat.card ↥⁅S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2),
      critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k) :
    ⁅S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2),
        critA _ (baseA (puAmalgam h.le)) α'⁆ ≤
      Subgroup.centralizer (S5.jOff h.le L (2 ^ k) μ ν : Set (puAmalgam h.le).Universal) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hδM : IsMVtx _ δ := isMVtx_geo_two _ hyp hb0 hc
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := dist_geo _ (by omega)
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  have hAν : critA _ (baseA (puAmalgam h.le)) α' ≤ Qv _ ν :=
    inf_le_right.trans (qv_le_qv _ hyp hα hαν)
  by_cases hZμ : ZM _ μ ≤ Qv _ δ
  · have hY : S5.uSub h.le L μ ⊓ Qv _ δ = S5.uSub h.le L μ :=
      inf_eq_left.2 ((uSub_le_zm h.le μ).trans hZμ)
    rw [hY] at hcard ⊢
    exact commutator_le_centralizer_jOff_one h hmin hb hd h54 hμ hνμ.symm hAν hcard.le
  ·
    have hdμβ : (puAmalgam h.le).treeGraph.dist μ (baseB _) < critDist (puAmalgam h.le) := by
      have h1 := dist_triangle _ μ ν (baseB (puAmalgam h.le))
      have h2 := dist_triangle _ ν (baseA (puAmalgam h.le)) (baseB (puAmalgam h.le))
      have e1 : (puAmalgam h.le).treeGraph.dist μ ν = 1 := dist_eq_one_of_adj _ hνμ.symm
      have e2 : (puAmalgam h.le).treeGraph.dist ν (baseA _) = 1 := dist_eq_one_of_adj _ hαν.symm
      have e3 : (puAmalgam h.le).treeGraph.dist (baseA (puAmalgam h.le)) (baseB _) = 1 :=
        dist_eq_one_of_adj _ hαβadj
      omega
    have hZμβ : ZM _ μ ≤ Qv _ (baseB (puAmalgam h.le)) := zm_le_qv_of_dist_lt _ hμ hdμβ
    have hCδ : Qv _ (baseB (puAmalgam h.le)) ⊓
        Subgroup.centralizer (ZM _ δ : Set (puAmalgam h.le).Universal) = Qv _ δ :=
      h.centHyp δ (baseB _) hδM hβδ.symm
    have hY : S5.uSub h.le L μ ⊓ Qv _ δ =
        S5.uSub h.le L μ ⊓ Subgroup.centralizer (ZM _ δ : Set (puAmalgam h.le).Universal) := by
      rw [← hCδ, ← inf_assoc, inf_eq_left.2 ((uSub_le_zm h.le μ).trans hZμβ)]
    have hdδν : (puAmalgam h.le).treeGraph.dist δ ν < critDist (puAmalgam h.le) := by
      have h1 := dist_triangle _ δ (baseA (puAmalgam h.le)) ν
      have e1 : (puAmalgam h.le).treeGraph.dist δ (baseA _) = 2 := by
        rw [SimpleGraph.dist_comm]
        exact hdδ
      have e2 : (puAmalgam h.le).treeGraph.dist (baseA (puAmalgam h.le)) ν = 1 :=
        dist_eq_one_of_adj _ hαν
      omega
    have hZδν : ZM _ δ ≤ Qv _ ν := zm_le_qv_of_dist_lt _ hδM hdδν
    have hZδQ : ¬ ZM _ δ ≤ Qv _ μ := by
      intro hle
      apply hZμ
      rw [← hCδ]
      refine le_inf hZμβ ?_
      rw [← Subgroup.le_centralizer_iff]
      exact hle.trans (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hμ))
    have hUδ : S5.uSub h.le L μ ≤ Subgroup.normalizer (ZM _ δ : Set (puAmalgam h.le).Universal) :=
      ((uSub_le_zm h.le μ).trans hZμβ).trans ((qv_le_stab_of_adj _ hβδ).trans
        (stab_le_normalizer_zm _ _))
    have hquad : ⁅⁅S5.uSub h.le L μ, ZM _ δ⁆, ZM _ δ⁆ = ⊥ := by
      have h1 : ⁅S5.uSub h.le L μ, ZM _ δ⁆ ≤ ZM _ δ := by
        rw [Subgroup.commutator_comm]
        exact commutator_le_left_of_le_normalizer hUδ
      have h2 : ⁅ZM (puAmalgam h.le) δ, ZM (puAmalgam h.le) δ⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.2
          ((zm_le_centralizer_qv _ hyp hδM).trans
            (Subgroup.centralizer_le (zm_le_qv_self _ hδM hb0)))
      exact le_bot_iff.1 ((Subgroup.commutator_mono h1 le_rfl).trans h2.le)
    have hAZ : critA _ (baseA (puAmalgam h.le)) α' ≤
        Subgroup.normalizer (ZM _ δ : Set (puAmalgam h.le).Universal) :=
      inf_le_right.trans ((qv_le_stab_of_dist_le_two _ hyp hα hdδ.le).trans
        (stab_le_normalizer_zm _ _))
    rw [hY]
    exact commutator_le_centralizer_jOff_two h hmin hb hd h54 hμ hνμ.symm hAν hZδν hZδQ hquad
      hAZ

end JFix

section Outer

omit [Fintype F] in
theorem outer_case55 (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4) {q : ℕ}
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {δ' : Vtx (puAmalgam h.le)}
    (hc' : IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hmem : baseA _ ∈ lamAllAt h q a (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hcase : ∀ l, ¬ S5.Case56 h q a (geo _ (baseA (puAmalgam h.le)) α' 2) l) :
    ZH _ (geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 1) ⊓
        Subgroup.centralizer (S5.jOff h.le L q (geo _ (baseA (puAmalgam h.le)) α' 2) (baseB _) :
          Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
    (puTrans h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
        S5.jOff h.le L q (baseA _) (baseB _) ⊔
          S5.zHat _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' ∨
      XM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≠
        S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ⊔
          XM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ⊓
            Subgroup.centralizer (puTrans h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) :
              Set (puAmalgam h.le).Universal)) := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hb0 := h.critDist_pos
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  set ε := geo _ δ δ' 1 with hε
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := dist_geo _ (by omega)
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨g₀, hg₀δ, hg₀ε, δ₀, hβδ₀, -, hδ₀⟩ := hmem
  obtain ⟨y, hy, hyδ₀⟩ := exists_mem_stab_of_mem_lam hδ₀
  have hyα : y • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hy
  have hdist : (puAmalgam h.le).treeGraph.dist (baseA _) (g₀ • baseA (puAmalgam h.le)) = 2 := by
    have := dist_smul _ g₀ δ (baseA (puAmalgam h.le))
    rw [hg₀δ] at this
    rw [this, SimpleGraph.dist_comm, hdδ]
  have hyβ : y • baseB (puAmalgam h.le) = g₀ • baseB (puAmalgam h.le) := by
    have h1 : (puAmalgam h.le).treeGraph.Adj (baseA _) (y • baseB (puAmalgam h.le)) := by
      have := (adj_smul _ y _ _).2 hαβadj
      rwa [hyα] at this
    have h2 : (puAmalgam h.le).treeGraph.Adj (y • baseB (puAmalgam h.le))
        (g₀ • baseA (puAmalgam h.le)) := by
      rw [hyδ₀]
      exact (adj_smul _ y _ _).2 hβδ₀
    have h3 : (puAmalgam h.le).treeGraph.Adj (baseA _) (g₀ • baseB (puAmalgam h.le)) := by
      have := (adj_smul _ g₀ _ _).2 hβδ.symm
      rwa [hg₀δ] at this
    have h4 : (puAmalgam h.le).treeGraph.Adj (g₀ • baseB (puAmalgam h.le))
        (g₀ • baseA (puAmalgam h.le)) := (adj_smul _ g₀ _ _).2 hαβadj.symm
    rw [eq_geo_one _ h1 (by rw [dist_eq_one_of_adj _ h2, hdist]),
      eq_geo_one _ h3 (by rw [dist_eq_one_of_adj _ h4, hdist])]
  set t := g₀⁻¹ * y * g₀ with ht
  have htδ : t • δ = δ := by
    rw [ht, mul_smul, mul_smul, hg₀δ, hyα, ← hg₀δ, inv_smul_smul]
  have htε : t • ε = baseB _ := by
    rw [ht, mul_smul, mul_smul, hg₀ε, hyβ, inv_smul_smul]
  have htδ₀ : t • (g₀⁻¹ • δ₀) = baseA _ := by
    rw [ht, mul_smul, mul_smul, smul_inv_smul, ← hyδ₀, inv_smul_smul]
  have hcase' : S5.jOff h.le L q (g₀⁻¹ • δ₀) ε ≠ S5.jOff h.le L q δ ε ∨ ¬ S510.LineCase h q a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hJ, hlc⟩ := hcon
    have e1 : S5.jOff h.le L q (baseA _) (baseB _) =
        (S5.jOff h.le L q (g₀⁻¹ • δ₀) ε).map (MulAut.conj t).toMonoidHom := by
      rw [← jOff_smul h.le hLn, htδ₀, htε]
    have e2 : S5.jOff h.le L q δ (baseB _) =
        (S5.jOff h.le L q δ ε).map (MulAut.conj t).toMonoidHom := by
      rw [← jOff_smul h.le hLn, htδ, htε]
    have hJδ : S5.jOff h.le L q δ (baseB _) = S5.jOff h.le L q (baseA _) (baseB _) := by
      rw [e1, e2, hJ]
    obtain ⟨l, hl⟩ := (S510.exists_case56_iff h q a δ).2 ⟨hJδ, hlc⟩
    exact hcase l hl
  have hγ : δ = g₀⁻¹ • baseA (puAmalgam h.le) := by rw [← hg₀δ, inv_smul_smul]
  have hε' : ε = g₀⁻¹ • baseB (puAmalgam h.le) := by rw [← hg₀ε, inv_smul_smul]
  have hεδ₀ : (puAmalgam h.le).treeGraph.Adj ε (g₀⁻¹ • δ₀) := by
    rw [hε']
    exact (adj_smul _ g₀⁻¹ _ _).2 hβδ₀
  have hμ : g₀⁻¹⁻¹ • baseA (puAmalgam h.le) ∈
      S5.lam h q a (g₀⁻¹⁻¹ • δ') (g₀⁻¹⁻¹ • g₀⁻¹ • δ₀) := by
    rw [inv_inv, smul_inv_smul]
    exact hδ₀
  obtain ⟨ν, hδν, hνα, -, -, hcen, hL⟩ := S510.loc55 h hc' hγ hε' hεδ₀ hcase' hμ
  have hνβ : ν = baseB _ := by
    have hdδα : (puAmalgam h.le).treeGraph.dist δ (baseA _) = 2 := by
      rw [SimpleGraph.dist_comm]
      exact hdδ
    rw [eq_geo_one _ hδν (by rw [dist_eq_one_of_adj _ hνα, hdδα]),
      eq_geo_one _ hβδ.symm (by rw [dist_eq_one_of_adj _ hαβadj.symm, hdδα])]
  subst hνβ
  exact ⟨hcen, hL.imp id fun h2 => h2.2.2⟩

end Outer

section Main

theorem commutator_vv_le_xm_at (h52 : S52) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    ⁅Vv (puAmalgam h.le) ρ, Vv (puAmalgam h.le) ρ⁆ ≤ XM _ ρ := by
  have h0 := (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.1
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  rw [show Vv (puAmalgam h.le) (g • baseA (puAmalgam h.le)) =
      (Vv (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom from vi_smul _ g _ 2,
    xm_smul, ← Subgroup.map_commutator, map_conj_le_map_conj_iff]
  exact h0

theorem relIndex_centralizer_zm_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _)
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k) :
    (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le))) = 2 ^ k := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hdist : (puAmalgam h.le).treeGraph.dist (baseA _) α' = critDist (puAmalgam h.le) :=
    hc.2.1
  have hcr := ms22_iii _ hyp hb0 hC hc
  have hd' : (puAmalgam h.le).treeGraph.dist α' (baseA _) = critDist (puAmalgam h.le) :=
    hcr.2.1
  set ε := geo _ α' (baseA (puAmalgam h.le)) 1 with hε
  have h1 : (puAmalgam h.le).treeGraph.Adj α' ε := adj_geo_one _ (by omega)
  have hda₁ : (puAmalgam h.le).treeGraph.dist (baseA _) ε < critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd']
    omega
  have hZαε : ZM _ (baseA (puAmalgam h.le)) ≤ Qv _ ε := zm_le_qv_of_dist_lt _ hα hda₁
  have hCε : Qv _ ε ⊓ Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal) =
      Qv _ α' := hC α' ε hα' h1
  obtain ⟨hZ'st, -, -, -, -, -⟩ := crit_facts h hc
  have hZ'T : ZM _ α' ≤ Qv _ (baseB (puAmalgam h.le)) := by
    refine zm_le_qv_of_dist_lt _ hα' ?_
    rw [← hαβ, SimpleGraph.dist_comm, dist_geo_right _ (by omega), hdist]
    omega
  have hZ'2 : IsPGroup 2 (ZM _ α') :=
    (isPGroup_qv _ hyp (not_isMVtx_baseB _)).to_le hZ'T
  have hZ'Q : ¬ ZM _ α' ≤ Qv _ (baseA (puAmalgam h.le)) := by
    intro hle
    apply hc.2.2
    rw [← hCε]
    refine le_inf hZαε ?_
    rw [← Subgroup.le_centralizer_iff]
    exact hle.trans (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα))
  refine le_antisymm ?_ (le_relIndex_centralizer h hd hα hZ'st hZ'2 hZ'Q)
  have hinf : Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal) ⊓
      ZM _ (baseA (puAmalgam h.le)) = Qv _ α' ⊓ ZM _ (baseA (puAmalgam h.le)) := by
    rw [← hCε, inf_comm (Qv _ ε), inf_assoc, inf_eq_right.2 hZαε]
  have e1 : (Subgroup.centralizer (ZM _ α' : Set (puAmalgam h.le).Universal)).relIndex
      (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k := by
    rw [← Subgroup.inf_relIndex_right, hinf, Subgroup.inf_relIndex_right, hidx]
  rw [← e1]
  exact Subgroup.relIndex_le_of_le_right (uSub_le_zm h.le _)
    (by rw [e1]; exact (Nat.pos_of_ne_zero (by positivity)).ne')

theorem s512One_case55 (h32 : S32) (hX2 : S33.S33X52) (h52 : S52) (h54 : S54)
    (h : PUHyp M T L) (hmin : PUMin M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {δ' : Vtx (puAmalgam h.le)}
    (hc' : IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hgeo : geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 2 = α')
    (hmem : baseA _ ∈ lamAllAt h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) δ')
    (hcase : ∀ l, ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    {μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2)) :
    S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
  by_contra hn
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα : IsMVtx _ (baseA (puAmalgam h.le)) := isMVtx_baseA _
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hαβadj := adj_baseA_baseB (puAmalgam h.le)
  set δ := geo _ (baseA (puAmalgam h.le)) α' 2 with hδ
  have hβδ : (puAmalgam h.le).treeGraph.Adj (baseB _) δ := by
    have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
    rwa [hαβ] at this
  have hδM : IsMVtx _ δ := isMVtx_geo_two _ hyp hb0 hc
  have hdδ : (puAmalgam h.le).treeGraph.dist (baseA _) δ = 2 := dist_geo _ (by omega)
  have hdδα' : (puAmalgam h.le).treeGraph.dist δ α' = 2 := by
    rw [dist_geo_right _ (by omega), hd4]
  have hgδ : geo _ α' (baseA (puAmalgam h.le)) 2 = δ := by
    have := geo_symm _ (show 2 ≤ (puAmalgam h.le).treeGraph.dist (baseA _) α' by omega)
    rwa [hd4] at this
  have hd' : (puAmalgam h.le).treeGraph.dist δ δ' = 4 := hc'.2.1.trans hb4
  set ε := geo _ δ δ' 1 with hε
  have hδε : (puAmalgam h.le).treeGraph.Adj δ ε := adj_geo_one _ (by omega)
  have hεα' : (puAmalgam h.le).treeGraph.Adj ε α' := by
    have := adj_geo _ (u := δ) (w := δ') (i := 1) (by omega)
    rwa [hgeo] at this
  have hδ'M : IsMVtx _ δ' := hc'.isMVtx_right _ hyp
  have hdδ'α' : (puAmalgam h.le).treeGraph.dist δ' α' = 2 := by
    rw [SimpleGraph.dist_comm, ← hgeo, dist_geo_right _ (by omega), hd']
  obtain ⟨ν, hαν, hνμ, ⟨t, ht, htβ, htδ⟩, -, -, hL⟩ := S510.lam55_facts h hc hβδ hcase hμ
  have hμM : IsMVtx _ μ := htδ ▸ (isMVtx_smul _ t _).2 hδM
  have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) μ = 2 := by
    have := dist_smul _ t (baseA (puAmalgam h.le)) δ
    rw [(mem_stab _).1 ht, htδ] at this
    rw [this, hdδ]
  have hn' : ¬ S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
      (((S5.uSub h.le L μ ⊓ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 2)) ⊔
        XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _) := by
    rw [hgδ]
    exact hn
  obtain ⟨hidx, hXU, hcard, hR1⟩ :=
    s512_s33 h32 hX2 h52 h hmin hb hd hc (by rw [hgδ]; exact hdδ) hμM hdμ hn'
  rw [hgδ] at hcard hR1
  have hXC : ∀ {ρ : Vtx (puAmalgam h.le)}, IsMVtx _ ρ → XM _ ρ = S5.uSub h.le L ρ ⊔ XM _ ρ ⊓
      Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) := fun hρ =>
    S5Q2.xm_eq_uSub_sup_centralizer h hXU hρ
  set Y := S5.uSub h.le L μ ⊓ Qv _ δ with hY
  set A := critA _ (baseA (puAmalgam h.le)) α' with hA
  set R := critR _ (baseA (puAmalgam h.le)) α' with hR
  obtain ⟨hZ'st, -, -, -, -, -⟩ := crit_facts h hc
  have hAQ : A ≤ Qv _ (baseA (puAmalgam h.le)) := inf_le_right
  have hAX : A ≤ XM _ α' := inf_le_left
  have hYZ : Y ≤ ZM _ μ := inf_le_left.trans (uSub_le_zm h.le μ)
  have hZμQ : ZM _ μ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hμM (by rw [SimpleGraph.dist_comm, hdμ]; omega)
  have hQαμ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ μ :=
    qv_le_stab_of_dist_le_two _ hyp hα hdμ.le
  have hQαδ : Qv _ (baseA (puAmalgam h.le)) ≤ stab _ δ :=
    qv_le_stab_of_dist_le_two _ hyp hα hdδ.le
  have hQδα' : Qv _ δ ≤ stab _ α' := qv_le_stab_of_dist_le_two _ hyp hδM hdδα'.le
  have hR₁X : ⁅Y, A⁆ ≤ XM _ α' := by
    refine (Subgroup.commutator_mono le_rfl hAX).trans ?_
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer
      ((inf_le_right.trans hQδα').trans (stab_le_normalizer_xm _ _))
  have hR₁Q : ⁅Y, A⁆ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    commutator_le_of_le (hYZ.trans hZμQ) hAQ
  have hJ := commutator_le_centralizer_jOff_mu h hmin hb4 hd h54 hc hαβ hμM hαν hνμ hcard
  have hL' : puTrans h.le L (baseA _) ≤
      S5.jOff h.le L (2 ^ k) μ ν ⊔ S5.zHat _ (baseA (puAmalgam h.le)) α' :=
    hL.resolve_right fun h2 => h2.2.2 (hXC hα)
  have hZhR : S5.zHat _ (baseA (puAmalgam h.le)) α' ≤
      Subgroup.centralizer ((⁅Y, A⁆ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hR₁X.trans ((xm_le_centralizer _ α').trans (Subgroup.centralizer_le
      (inf_le_left.trans (zm_le_qv_self _ hα' hb0))))
  have hR₁L : ⁅Y, A⁆ ≤ Subgroup.centralizer (puTrans h.le L (baseA _) : Set _) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hL'.trans (sup_le (Subgroup.le_centralizer_iff.1 hJ) hZhR)
  obtain ⟨l, hl, t₀, ht₀, rfl⟩ := exists_puTrans_mul h hαβadj ht
  have hlδ : l • δ = μ := by
    rw [← htδ, mul_smul, (mem_stab _).1 (qv_le_stab_of_adj _ hβδ ht₀)]
  have hlβ : l • baseB (puAmalgam h.le) = ν := by
    rw [← htβ, mul_smul, (mem_stab _).1 (qv_le_stab _ _ ht₀)]
  have hlc : ∀ r ∈ ⁅Y, A⁆, l * r * l⁻¹ = r := fun r hr => by
    rw [Subgroup.mem_centralizer_iff.1 (hR₁L hr) l hl, mul_inv_cancel_right]
  have hJδ : ⁅Y, A⁆ ≤ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) δ (baseB _) : Set (puAmalgam h.le).Universal) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    have hj' : l * j * l⁻¹ ∈ S5.jOff h.le L (2 ^ k) μ ν := by
      rw [← hlδ, ← hlβ, jOff_smul h.le hLn]
      exact ⟨j, hj, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (hJ hr) _ hj'
    have h2 := hlc r hr
    have hr' : l⁻¹ * r * l = r := by
      calc l⁻¹ * r * l = l⁻¹ * (l * r * l⁻¹) * l := by rw [h2]
        _ = r := by group
    calc j * r = l⁻¹ * ((l * j * l⁻¹) * (l * r * l⁻¹)) * l := by group
      _ = l⁻¹ * (r * (l * j * l⁻¹)) * l := by rw [h2, h1]
      _ = (l⁻¹ * r * l) * j := by group
      _ = r * j := by rw [hr']
  obtain ⟨hcen_o, hL_o⟩ := outer_case55 h hb4 hc hαβ hc' hmem hcase
  have hL_o' : puTrans h.le L δ ≤ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ⊔ S5.zHat _ δ δ' :=
    hL_o.resolve_right fun h2 => h2 (hXC hδM)
  have hZ'T : ZM _ α' ≤ Qv _ (baseB (puAmalgam h.le)) := by
    refine zm_le_qv_of_dist_lt _ hα' ?_
    rw [← hαβ, SimpleGraph.dist_comm, dist_geo_right _ (by omega), hd4]
    omega
  have hrel := relIndex_centralizer_zm_eq h hd hc hαβ hidx
  have hRJ : R ≤ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set (puAmalgam h.le).Universal) :=
    (critR_le_commutator_uSub h hb hc hαβ).trans
      (commutator_le_centralizer_jOff_of_relIndex_baseA h hmin hb hd h54 hZ'T hrel)
  have hRZ' : R ≤ ZM _ α' := by
    rw [hR, critR, Subgroup.commutator_comm]
    refine commutator_le_left_of_le_normalizer ?_
    exact ((zm_le_qv_of_dist_lt _ hα (by omega)).trans hQδα').trans (stab_le_normalizer_zm _ _)
  have hRZα : R ≤ ZM _ (baseA (puAmalgam h.le)) :=
    commutator_le_left_of_le_normalizer (hZ'st.trans (stab_le_normalizer_zm _ _))
  have hRZh : R ≤ Subgroup.centralizer (S5.zHat _ δ δ' : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.le_centralizer_iff]
    exact (inf_le_left.trans (zm_le_qv_of_dist_lt _ hδ'M (by omega))).trans
      ((qv_le_centralizer_xm _ α').trans (Subgroup.centralizer_le
        (hRZ'.trans (zm_le_xm _ hyp hb0 hα'))))
  have hRL : R ≤ Subgroup.centralizer (puTrans h.le L δ : Set (puAmalgam h.le).Universal) := by
    rw [← Subgroup.le_centralizer_iff]
    exact hL_o'.trans (sup_le (Subgroup.le_centralizer_iff.1 hRJ)
      (Subgroup.le_centralizer_iff.1 hRZh))
  have hRQ : R ≤ Qv _ δ := hRZα.trans (zm_le_qv_of_dist_lt _ hα (by omega))
  have hRX : R ≤ XM _ δ := by
    refine le_trans ?_ (commutator_vv_le_xm_at h52 h hmin hb hd hc hδM)
    exact Subgroup.commutator_mono (zm_le_vv_of_dist hα (by rw [SimpleGraph.dist_comm, hdδ]))
      (zm_le_vv_of_dist hα' hdδα'.le)
  have hRZG : R ≤ stabCenter _ δ := fun r hr =>
    S5Q2.xm_inf_centralizer_le_stabCenter h (S5Q2.UC.zq_le_centralizer_of_relIndex_eq h hd hc hidx)
      hδM ⟨hRX hr, hRL hr⟩
  have hRZε : R ≤ ZH _ ε := fun r hr => stabCenter_inf_xm_le_zh h hδM hδε ⟨hRZG hr, hRX hr⟩
  have hRX' : R ≤ XM _ α' := hRZ'.trans (zm_le_xm _ hyp hb0 hα')
  have hR₁Zε : ⁅Y, A⁆ ≤ ZH _ ε := by
    intro r₁ hr₁
    have h1 := hR1 hr₁
    have hRst : R ≤ stab _ α' := hRZ'.trans ((zm_le_qv_self _ hα' hb0).trans (qv_le_stab _ _))
    have hZn : stabCenter _ α' ≤ Subgroup.normalizer (R : Set (puAmalgam h.le).Universal) :=
      (stabCenter_le_inf α').trans (inf_le_right.trans ((Subgroup.centralizer_le hRst).trans
        (Subgroup.centralizer_le_normalizer _)))
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZn] at h1
    obtain ⟨r, hr, z, hz, rfl⟩ := h1
    have hzX : z ∈ XM _ α' := by
      have e : z = r⁻¹ * (r * z) := by group
      rw [e]
      exact mul_mem (inv_mem (hRX' hr)) (hR₁X hr₁)
    exact mul_mem (hRZε hr) (stabCenter_inf_xm_le_zh h hα' hεα'.symm ⟨hz, hzX⟩)
  have hR₁ZG : ⁅Y, A⁆ ≤ stabCenter _ δ := fun r hr => hcen_o ⟨hR₁Zε hr, hJδ hr⟩
  have hR₁Zμ : ⁅Y, A⁆ ≤ stabCenter _ μ := by
    intro r hr
    rw [← hlδ, S510.stabCenter_smul]
    refine ⟨r, hR₁ZG hr, ?_⟩
    show l * r * l⁻¹ = r
    exact hlc r hr
  have hbot : ⁅Y, A⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy a' ha'
    have hc1 : ⁅y, a'⁆ ∈ ⁅Y, A⁆ := Subgroup.commutator_mem_commutator hy ha'
    have hmem1 : a' * y * a'⁻¹ * y⁻¹ ∈ Subgroup.centralizer
        (puTrans h.le L μ : Set (puAmalgam h.le).Universal) := by
      have e : a' * y * a'⁻¹ * y⁻¹ = ⁅y, a'⁆⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      refine inv_mem (Subgroup.mem_centralizer_iff.2 fun x hx => ?_)
      exact S510.commute_of_mem_stabCenter (hR₁Zμ hc1) (puTrans_le_stab h.le L μ hx)
    have h1 := lift_at h hd hμM (hQαμ (hAQ ha')) hy.1 hmem1
    have h2 : y * a' = a' * y := by
      calc y * a' = (a' * y * a'⁻¹) * a' := by rw [h1]
        _ = a' * y := by group
    rw [Subgroup.mem_bot, commutatorElement_def, h2]
    group
  rw [hbot, Subgroup.card_bot] at hcard
  exact absurd hcard (Nat.one_lt_two_pow (by have := hd.1; omega)).ne

end Main

end S5B

end CFSG.Quasithin.MS93

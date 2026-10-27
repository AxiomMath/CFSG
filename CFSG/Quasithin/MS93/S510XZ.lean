module

public import CFSG.Quasithin.MS93.S510R1
public import CFSG.Quasithin.MS93.S510LX

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S510

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Vertex

theorem uSub_inf_le_stabCenter (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) :
    S5.uSub h.le L ρ ⊓ Subgroup.centralizer (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ ρ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hUM := (sp4Lift_holds G M T L h k F _ _ a hd).2.1
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  rw [S5B.uSub_smul h.le hLn, puTrans_smul h.le hLn, PU.centralizer_map_mulEquiv,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective, stabCenter_smul,
    map_conj_le_map_conj_iff, S5B.uSub_baseA h, S5B.puTrans_L_baseA h,
    ← imM_inf_centralizer h.le _ h.L_le, hUM, S5B.stabCenter_baseA]
  exact imM_mono h.le (inf_le_inf_right _ (Uq_le h.L_le))

theorem lift_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {m u : (puAmalgam h.le).Universal} (hm : m ∈ stab _ (baseA (puAmalgam h.le)))
    (hu : u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)))
    (hc : m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer
      (puTrans h.le L (baseA (puAmalgam h.le)) : Set (puAmalgam h.le).Universal)) :
    m * u * m⁻¹ = u := by
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  rw [puAmalgam.stab_baseA] at hm
  rw [S5B.uSub_baseA h] at hu
  rw [S5B.puTrans_L_baseA h] at hc
  obtain ⟨m₀, -, rfl⟩ := hm
  obtain ⟨u₀, hu₀, rfl⟩ := hu
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

theorem lift_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) {m u : (puAmalgam h.le).Universal}
    (hm : m ∈ stab _ ρ) (hu : u ∈ S5.uSub h.le L ρ)
    (hc : m * u * m⁻¹ * u⁻¹ ∈ Subgroup.centralizer
      (puTrans h.le L ρ : Set (puAmalgam h.le).Universal)) :
    m * u * m⁻¹ = u := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hρ
  rw [mem_stab_smul] at hm
  rw [S5B.uSub_smul h.le hLn, mem_map_conj] at hu
  rw [puTrans_smul h.le hLn, PU.centralizer_map_mulEquiv, mem_map_conj] at hc
  have e : g⁻¹ * (m * u * m⁻¹ * u⁻¹) * g =
      (g⁻¹ * m * g) * (g⁻¹ * u * g) * (g⁻¹ * m * g)⁻¹ * (g⁻¹ * u * g)⁻¹ := by group
  rw [e] at hc
  have h1 := lift_baseA h hd hm hu hc
  calc m * u * m⁻¹ = g * ((g⁻¹ * m * g) * (g⁻¹ * u * g) * (g⁻¹ * m * g)⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * u * g) * g⁻¹ := by rw [h1]
    _ = u := by group

omit [Fintype F] in
theorem exists_mul_of_mem_sup (h : PUHyp M T L) {ρ : Vtx (puAmalgam h.le)}
    {x : (puAmalgam h.le).Universal}
    (hx : x ∈ S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ) :
    ∃ u ∈ S5.uSub h.le L ρ, ∃ c ∈ stabCenter _ ρ, x = u * c := by
  have hle : XM _ ρ ⊓ stabCenter _ ρ ≤
      Subgroup.normalizer (S5.uSub h.le L ρ : Set (puAmalgam h.le).Universal) :=
    inf_le_right.trans ((Subgroup.map_subtype_le _).trans (stab_le_normalizer_uSub h ρ))
  have hx' : x ∈ ((S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ : Subgroup _) :
      Set (puAmalgam h.le).Universal) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hx'
  obtain ⟨u, hu, c, hc, rfl⟩ := hx'
  exact ⟨u, hu, c, hc.2, rfl⟩

theorem liftX_gp (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {ρ : Vtx (puAmalgam h.le)}
    (hρ : IsMVtx _ ρ) {m x : (puAmalgam h.le).Universal} (hm : m ∈ stab _ ρ)
    (hx : x ∈ S5.uSub h.le L ρ ⊔ XM _ ρ ⊓ stabCenter _ ρ) :
    m * x * m⁻¹ * x⁻¹ ∈ S5.uSub h.le L ρ ∧
      (m * x * m⁻¹ * x⁻¹ ∈ Subgroup.centralizer
        (puTrans h.le L ρ : Set (puAmalgam h.le).Universal) → m * x * m⁻¹ = x) := by
  obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup h hx
  have hmc : m * c = c * m := commute_of_mem_stabCenter hc hm
  have e : m * (u * c) * m⁻¹ * (u * c)⁻¹ = m * u * m⁻¹ * u⁻¹ := by
    have : c * m⁻¹ = m⁻¹ * c := by
      calc c * m⁻¹ = m⁻¹ * (m * c) * m⁻¹ := by group
        _ = m⁻¹ * (c * m) * m⁻¹ := by rw [hmc]
        _ = m⁻¹ * c := by group
    calc m * (u * c) * m⁻¹ * (u * c)⁻¹ = m * u * (c * m⁻¹) * c⁻¹ * u⁻¹ := by group
      _ = m * u * (m⁻¹ * c) * c⁻¹ * u⁻¹ := by rw [this]
      _ = m * u * m⁻¹ * u⁻¹ := by group
  have hconj : m * u * m⁻¹ ∈ S5.uSub h.le L ρ :=
    (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_uSub h ρ hm) u).1 hu
  rw [e]
  refine ⟨mul_mem hconj (inv_mem hu), fun hcL => ?_⟩
  have h1 := lift_gp h hd hρ hm hu hcL
  calc m * (u * c) * m⁻¹ = m * u * m⁻¹ * (m * c * m⁻¹) := by group
    _ = u * c := by rw [h1, hmc]; group

theorem critA_le_of_relIndex (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ')
    (hidx : (Qv _ γ').relIndex (ZM _ γ) = 2 ^ k) :
    critA _ γ γ' ≤ S5.uSub h.le L γ' ⊔ XM _ γ' ⊓ stabCenter _ γ' ∧ critA _ γ γ' ≤ ZM _ γ' := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  rcases Nat.lt_or_ge k 2 with hk | hk
  · obtain rfl : k = 1 := by have := hd.1; omega
    have hc' := ms22_iii _ hyp hb0 h.centHyp hc
    have hidx' := S5Q2.relIndex_qv_zm_le_two h hd hc (by rw [hidx]; norm_num)
    have hAC : critA _ γ γ' ≤
        XM _ γ' ⊓ Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) :=
      le_inf inf_le_left (inf_le_right.trans
        (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hc.1)))
    exact ⟨hAC.trans (S5Q2.xm_inf_centralizer_zm_le h hd hXU hc' hidx'),
      hAC.trans (S5Q2.xm_inf_centralizer_zm_le_zm h hd hXU hc' hidx')⟩
  · have e := xm_eq_gp_of h hXU (S5Q2.zq_le_centralizer_of_two_le h hd hk)
      (hc.isMVtx_right _ hyp)
    exact ⟨inf_le_left.trans e.1.le, inf_le_left.trans e.2.le⟩

omit [Fintype F] in
theorem critR_le_uSub (h : PUHyp M T L) {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    critR _ γ γ' ≤ S5.uSub h.le L γ := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist γ γ' = critDist (puAmalgam h.le) := hc.2.1
  have hadj : (puAmalgam h.le).treeGraph.Adj γ (geo _ γ γ' 1) := adj_geo_one _ (by omega)
  have hZQ : ZM _ γ' ≤ Qv _ (geo _ γ γ' 1) :=
    zm_le_qv_of_dist_lt _ (hc.isMVtx_right _ hyp)
      (by rw [tdist_comm, dist_geo_right _ (by omega), hd]; omega)
  have hN := stab_le_normalizer_uSub h γ
  rw [critR, S5B.zm_eq_zh_sup_uSub h hc.1 hadj]
  refine S5B.commutator_sup_le_of_le ((zh_le_zm _ hadj).trans
    ((zm_le_qv_self _ hc.1 hb0).trans ((qv_le_stab _ _).trans hN))) Subgroup.le_normalizer ?_ ?_
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer.2
      ((zh_le_centralizer _ _).trans (Subgroup.centralizer_le hZQ))]
    exact bot_le
  · exact commutator_le_left_of_le_normalizer ((zm_le_stab_of_isCritical _ hyp hb0 hc).trans hN)

end Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

namespace IsChain

variable {k : ℕ} {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}
  {h : PUHyp M T L} {q : ℕ} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem uSub_inf_le_qv (hch : IsChain h q a s t N) {m : ℕ} (hm : m + 1 ≤ N) :
    S5.uSub h.le L (geo _ s t (2 * m)) ⊓ Subgroup.centralizer
        (ZM _ (geo _ s t (2 * m + critDist (puAmalgam h.le))) : Set (puAmalgam h.le).Universal) ≤
      Qv _ (geo _ s t (2 * m + critDist (puAmalgam h.le) + 1)) := by
  have hdd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hb2 : 2 ≤ b := two_le_critDist _ hyp hb0
  have hμM : IsMVtx _ (P (2 * m)) := hch.isMVtx_P (by omega)
  have hμ'M : IsMVtx _ (P (2 * m + b)) := (hch.crit m (by omega)).isMVtx_right _ hyp
  have hadj' : (puAmalgam h.le).treeGraph.Adj (P (2 * m + b)) (P (2 * m + b + 1)) :=
    hch.adj_P (by omega)
  have hadj'' : (puAmalgam h.le).treeGraph.Adj (P (2 * m + b)) (P (2 * m + b - 1)) := by
    have := hch.adj_P (i := 2 * m + b - 1) (by omega)
    rw [show 2 * m + b - 1 + 1 = 2 * m + b by omega] at this
    exact this.symm
  have hZμ : ZM _ (P (2 * m)) ≤ Qv _ (P (2 * m + b - 1)) :=
    zm_le_qv_of_dist_lt _ hμM (by rw [hch.dist_P (by omega) (by omega)]; omega)
  have hYQ : S5.uSub h.le L (P (2 * m)) ⊓ Subgroup.centralizer
      (ZM _ (P (2 * m + b)) : Set (puAmalgam h.le).Universal) ≤ Qv _ (P (2 * m + b)) :=
    le_qv_of_le_centralizer _ hC hμ'M hadj''
      (inf_le_left.trans ((S5B.uSub_le_zm h.le _).trans hZμ)) inf_le_right
  exact hYQ.trans (qv_le_qv _ hyp hμ'M hadj')

theorem localX_step (h32 : S32) (hX2 : S33.S33X52) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) [Fintype F] (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) (hlc : LineCase h (2 ^ k) a)
    (hJq : (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)))
    {m : ℕ} (hm : m + 2 ≤ N) :
    ⁅S5.uSub h.le L (geo _ s t (2 * m)) ⊓ Subgroup.centralizer
          (ZM _ (geo _ s t (2 * m + critDist (puAmalgam h.le))) : Set _),
        critA _ (geo _ s t (2 * m + 2)) (geo _ s t (2 * m + critDist (puAmalgam h.le) + 2))⁆ ≤
        Subgroup.centralizer
          (S5.jOff h.le L (2 ^ k) (geo _ s t (2 * m)) (geo _ s t (2 * m + 1)) : Set _) ∧
      S5.uSub h.le L (geo _ s t (2 * m)) ⊓
          Subgroup.centralizer (puTrans h.le L (geo _ s t (2 * m)) : Set _) ≤
        ⁅S5.uSub h.le L (geo _ s t (2 * m)), ZM _ (geo _ s t (2 * m + critDist (puAmalgam h.le)))⁆ ⊔
          ⁅S5.uSub h.le L (geo _ s t (2 * m)) ⊓ Subgroup.centralizer
              (ZM _ (geo _ s t (2 * m + critDist (puAmalgam h.le))) : Set _),
            critA _ (geo _ s t (2 * m + 2)) (geo _ s t (2 * m + critDist (puAmalgam h.le) + 2))⁆ ∧
      ⁅S5.uSub h.le L (geo _ s t (2 * m)) ⊓ Subgroup.centralizer
          (ZM _ (geo _ s t (2 * m + critDist (puAmalgam h.le))) : Set _),
        critA _ (geo _ s t (2 * m + 2)) (geo _ s t (2 * m + critDist (puAmalgam h.le) + 2))⁆ ≤
        ZM _ (geo _ s t (2 * m + critDist (puAmalgam h.le) + 2)) := by
  have hdd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hb2 : 2 < b := by omega
  have hs : IsMVtx _ s := by
    have := (hch.crit 0 (Nat.zero_le _)).1
    rwa [Nat.mul_zero, geo_zero] at this
  have hbev : Even b := by
    have h1 := (hch.crit 0 (Nat.zero_le _)).isMVtx_right _ hyp
    rw [Nat.mul_zero, zero_add, isMVtx_geo _ (by omega)] at h1
    exact h1.1 hs
  have hMV : ∀ i, Even i → i ≤ b + 2 * N → IsMVtx _ (P i) := by
    intro i hi hiN
    rw [isMVtx_geo _ (by omega)]
    exact iff_of_true hs hi
  have hρM : IsMVtx _ (P (2 * m)) := hch.isMVtx_P (by omega)
  have hγM : IsMVtx _ (P (2 * m + 2)) := hMV _ ⟨m + 1, by ring⟩ (by omega)
  have hρ'M : IsMVtx _ (P (2 * m + b)) := hMV _ (by
    obtain ⟨c, hc⟩ := hbev; exact ⟨m + c, by omega⟩) (by omega)
  have hγ'M : IsMVtx _ (P (2 * m + b + 2)) := hMV _ (by
    obtain ⟨c, hc⟩ := hbev; exact ⟨m + c + 1, by omega⟩) (by omega)
  have hγ''M : IsMVtx _ (P (2 * m + b + 4)) := hMV _ (by
    obtain ⟨c, hc⟩ := hbev; exact ⟨m + c + 2, by omega⟩) (by omega)
  have hr1 := hch.r1_facts h32 hX2 h54 h59 hmin hd hb hcase hXU (i := m + 1) (by omega)
    (by omega)
  rw [show 2 * (m + 1) + b = 2 * m + b + 2 by ring, show 2 * (m + 1) - 2 + b = 2 * m + b by omega,
    show 2 * (m + 1) - 2 = 2 * m by omega, show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
    show 2 * (m + 1) = 2 * m + 2 by ring] at hr1
  obtain ⟨-, hidx, hcard, -⟩ := hr1
  set Y := S5.uSub h.le L (P (2 * m)) ⊓
    Subgroup.centralizer (ZM _ (P (2 * m + b)) : Set (puAmalgam h.le).Universal) with hY
  set A := critA _ (P (2 * m + 2)) (P (2 * m + b + 2)) with hA
  have hR : ⁅Y, A⁆ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
    omega
  have hadjρ : (puAmalgam h.le).treeGraph.Adj (P (2 * m)) (P (2 * m + 1)) := hch.adj_P (by omega)
  have hadjγ : (puAmalgam h.le).treeGraph.Adj (P (2 * m + 1)) (P (2 * m + 2)) :=
    hch.adj_P (by omega)
  have hE : ZM _ (P (2 * m + b)) ≤ Qv _ (P (2 * m + 1)) :=
    zm_le_qv_of_dist_lt _ hρ'M (by rw [tdist_comm, hch.dist_P (by omega) (by omega)]; omega)
  have hAQ : A ≤ Qv _ (P (2 * m + 1)) := inf_le_right.trans (qv_le_qv _ hyp hγM hadjγ.symm)
  have hrel := hch.partA hd hb hcase (j := m) (by omega)
  have hcrγ : IsCritical _ (P (2 * m + 2)) (P (2 * m + b + 2)) := by
    have := hch.crit (m + 1) (by omega)
    rwa [show 2 * (m + 1) + b = 2 * m + b + 2 by ring, show 2 * (m + 1) = 2 * m + 2 by ring]
      at this
  have hAZ : A ≤ ZM _ (P (2 * m + b + 2)) := (critA_le_of_relIndex h hd hXU hcrγ hidx).2
  have hYst : Y ≤ stab _ (P (2 * m + b + 2)) :=
    (hch.uSub_inf_le_qv (m := m) (by omega)).trans
      (qv_le_stab_of_adj _ (hch.adj_P (i := 2 * m + b + 1) (by omega)))
  have hRZ : ⁅Y, A⁆ ≤ ZM _ (P (2 * m + b + 2)) :=
    (Subgroup.commutator_mono le_rfl hAZ).trans (commutator_le_zm_of_le_stab hYst)
  have hcr := hch.crit m (by omega)
  have hUρ' : S5.uSub h.le L (P (2 * m)) ≤ stab _ (P (2 * m + b)) :=
    (S5B.uSub_le_zm h.le _).trans (zm_le_stab_of_isCritical _ hyp hb0
      (ms22_iii _ hyp hb0 hC hcr))
  have hWZ : ⁅S5.uSub h.le L (P (2 * m)), ZM _ (P (2 * m + b))⁆ ≤ ZM _ (P (2 * m + b)) :=
    commutator_le_zm_of_le_stab hUρ'
  have hRU : ⁅Y, A⁆ ≤ S5.uSub h.le L (P (2 * m)) :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans (commutator_le_left_of_le_normalizer
      (hAQ.trans ((qv_le_stab_of_adj _ hadjρ.symm).trans (stab_le_normalizer_uSub h _))))
  have hWU : ⁅S5.uSub h.le L (P (2 * m)), ZM _ (P (2 * m + b))⁆ ≤ S5.uSub h.le L (P (2 * m)) :=
    commutator_le_left_of_le_normalizer
      (hE.trans ((qv_le_stab_of_adj _ hadjρ.symm).trans (stab_le_normalizer_uSub h _)))
  have hd2 : (puAmalgam h.le).treeGraph.dist (P (2 * m + b)) (P (2 * m + b + 2)) = 2 := by
    rw [hch.dist_P (by omega) (by omega)]; omega
  have hd4 : (puAmalgam h.le).treeGraph.dist (P (2 * m + b)) (P (2 * m + b + 4)) = 4 := by
    rw [hch.dist_P (by omega) (by omega)]; omega
  have hd2' : (puAmalgam h.le).treeGraph.dist (P (2 * m + b + 2)) (P (2 * m + b + 4)) = 2 := by
    rw [hch.dist_P (by omega) (by omega)]; omega
  have hRW2 : ⁅Y, A⁆ ⊔ ⁅S5.uSub h.le L (P (2 * m)), ZM _ (P (2 * m + b))⁆ ≤
      Subgroup.centralizer (ZM _ (P (2 * m + b + 2)) : Set (puAmalgam h.le).Universal) :=
    sup_le (hRZ.trans (zm_le_centralizer_zm hyp hb0 hγ'M))
      (hWZ.trans (zm_le_centralizer_zm_of_dist hyp hb0 hρ'M hγ'M (by omega)))
  have hRW4 : ⁅Y, A⁆ ⊔ ⁅S5.uSub h.le L (P (2 * m)), ZM _ (P (2 * m + b))⁆ ≤
      Subgroup.centralizer (ZM _ (P (2 * m + b + 4)) : Set (puAmalgam h.le).Universal) :=
    sup_le (hRZ.trans (zm_le_centralizer_zm_of_dist hyp hb0 hγ'M hγ''M (by omega)))
      (hWZ.trans (zm_le_centralizer_zm_of_dist hyp hb0 hρ'M hγ''M (by omega)))
  have hsing : ∀ {w : (puAmalgam h.le).Universal} {Z : Subgroup (puAmalgam h.le).Universal},
      w ∈ Subgroup.centralizer (Z : Set (puAmalgam h.le).Universal) →
        Z ≤ Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal) := by
    intro w Z hw z hz
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hw z hz)
  have hcen : (⁅Y, A⁆ ⊔ ⁅S5.uSub h.le L (P (2 * m)), ZM _ (P (2 * m + b))⁆) ⊓
      Subgroup.centralizer (Qv _ (P (2 * m + 1)) : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (P (2 * m)) := by
    rintro w ⟨hw, hwT⟩
    refine hch.mem_stabCenter_of hcase (j := m) hm ?_ hwT (hsing (hRW2 hw)) (hsing (hRW4 hw))
    exact (S5B.uSub_le_zm h.le _).trans (zm_le_qv_self _ hρM hb0 |>.trans (qv_le_stab _ _))
      (sup_le hRU hWU hw)
  obtain ⟨h1, h2⟩ := localX_gp h hd hlc hJq hρM hadjρ hE hAQ hrel hcen hR
  exact ⟨h1, h2, hRZ⟩

theorem uSub_inf_le_stabCenter_all (h32 : S32) (hX2 : S33.S33X52) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) [Fintype F] (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) (hlc : LineCase h (2 ^ k) a)
    (hJq : (2 ^ k) ^ 2 ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)))
    {m : ℕ} (hm : m + 2 ≤ N) :
    ∀ m' ≤ N, S5.uSub h.le L (geo _ s t (2 * m)) ⊓
        Subgroup.centralizer (puTrans h.le L (geo _ s t (2 * m)) : Set _) ≤
      stabCenter _ (geo _ s t (2 * m')) := by
  have hdd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  obtain ⟨-, hX, -⟩ := hch.localX_step h32 hX2 h54 h59 hmin hd hb hcase hXU hlc hJq hm
  have hρM : IsMVtx _ (P (2 * m)) := hch.isMVtx_P (by omega)
  intro m' hm' w hw
  have hw0 : w ∈ stabCenter _ (P (2 * m)) := uSub_inf_le_stabCenter h hd hρM hw
  have hg := (hch.facts55 (j := m + 1) (by omega) (by omega) (hcase (m + 1) (by omega))).1
  rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, show 2 * (m + 1) + b = 2 * m + b + 2 by ring,
    show 2 * (m + 1) = 2 * m + 2 by ring] at hg
  have hadjρ : (puAmalgam h.le).treeGraph.Adj (P (2 * m)) (P (2 * m + 1)) := hch.adj_P (by omega)
  have hadjγ : (puAmalgam h.le).treeGraph.Adj (P (2 * m + 1)) (P (2 * m + 2)) :=
    hch.adj_P (by omega)
  have hwst2 : w ∈ stab _ (P (2 * m + 2)) :=
    (((S5B.uSub_le_zm h.le _).trans (zm_le_qv_of_dist_lt _ hρM
      (by rw [hch.dist_P (by omega) (by omega)]; omega))).trans (qv_le_stab_of_adj _ hadjγ))
      hw.1
  have hwZ : w ∈ Subgroup.centralizer
      (ZM _ (P (2 * m + b + 2)) : Set (puAmalgam h.le).Universal) := by
    have hsub := hX hw
    have hs : IsMVtx _ s := by
      have := (hch.crit 0 (Nat.zero_le _)).1
      rwa [Nat.mul_zero, geo_zero] at this
    have hbev : Even b := by
      have h1 := (hch.crit 0 (Nat.zero_le _)).isMVtx_right _ hyp
      rw [Nat.mul_zero, zero_add, isMVtx_geo _ (by omega)] at h1
      exact h1.1 hs
    have hMV : ∀ i, Even i → i ≤ b + 2 * N → IsMVtx _ (P i) := by
      intro i hi hiN
      rw [isMVtx_geo _ (by omega)]
      exact iff_of_true hs hi
    have hρ'M : IsMVtx _ (P (2 * m + b)) := hMV _ (by
      obtain ⟨c, hc⟩ := hbev; exact ⟨m + c, by omega⟩) (by omega)
    have hγ'M : IsMVtx _ (P (2 * m + b + 2)) := hMV _ (by
      obtain ⟨c, hc⟩ := hbev; exact ⟨m + c + 1, by omega⟩) (by omega)
    have hcr := hch.crit m (by omega)
    have hUρ' : S5.uSub h.le L (P (2 * m)) ≤ stab _ (P (2 * m + b)) :=
      (S5B.uSub_le_zm h.le _).trans (zm_le_stab_of_isCritical _ hyp hb0
        (ms22_iii _ hyp hb0 h.centHyp hcr))
    have hW : ⁅S5.uSub h.le L (P (2 * m)), ZM _ (P (2 * m + b))⁆ ≤
        Subgroup.centralizer (ZM _ (P (2 * m + b + 2)) : Set (puAmalgam h.le).Universal) :=
      (commutator_le_zm_of_le_stab hUρ').trans (zm_le_centralizer_zm_of_dist hyp hb0 hρ'M hγ'M
        (by rw [hch.dist_P (by omega) (by omega)]; omega))
    obtain ⟨-, -, hRZ⟩ := hch.localX_step h32 hX2 h54 h59 hmin hd hb hcase hXU hlc hJq hm
    exact sup_le hW (hRZ.trans (zm_le_centralizer_zm hyp hb0 hγ'M)) hsub
  have hw2 : w ∈ stabCenter _ (P (2 * m + 2)) := by
    rw [mem_stabCenter_iff]
    refine ⟨hwst2, fun y hy => ?_⟩
    rw [← hg] at hy
    have hle : Qv _ (P (2 * m + 1)) ⊔ ZM _ (P (2 * m + b + 2)) ≤
        Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (commute_of_mem_stabCenter hw0 (qv_le_stab_of_adj _ hadjρ.symm hx))
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 hwZ x hx)
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)
  exact hch.mem_stabCenter_all (i := m) (by omega) hw0 hw2 m' hm'

theorem false_of_xz (h32 : S32) (hX2 : S33.S33X52) (h54 : S54) (h59 : S5B.S59)
    (hmin : PUMin M T L) [Fintype F] (hd : S5.IsSp4Data M T L k F a)
    (hch : IsChain h (2 ^ k) a s t N) (hb : 4 < critDist (puAmalgam h.le))
    (hN : critDist (puAmalgam h.le) + 6 ≤ 2 * N)
    (hcase : ∀ j ≤ N, S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L (2 ^ k) (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨
          ¬ LineCase h (2 ^ k) a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) : False := by
  have hdd := hch.dist_eq
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hb2 : 2 < b := by omega
  have hs : IsMVtx _ s := by
    have := (hch.crit 0 (Nat.zero_le _)).1
    rwa [Nat.mul_zero, geo_zero] at this
  obtain ⟨c, hc⟩ : Even b := by
    have h1 := (hch.crit 0 (Nat.zero_le _)).isMVtx_right _ hyp
    rw [Nat.mul_zero, zero_add, isMVtx_geo _ (by omega)] at h1
    exact h1.1 hs
  have hρ0 : IsMVtx _ (P (2 * 0)) := hch.isMVtx_P (by omega)
  have hadj0 : (puAmalgam h.le).treeGraph.Adj (P (2 * 0)) (P (2 * 0 + 1)) := hch.adj_P (by omega)
  have hE0 : ZM _ (P (2 * 0 + b)) ≤ Qv _ (P (2 * 0 + 1)) :=
    zm_le_qv_of_dist_lt _ ((hch.crit 0 (by omega)).isMVtx_right _ hyp)
      (by rw [tdist_comm, hch.dist_P (by omega) (by omega)]; omega)
  have hrel0 := hch.partA hd hb hcase (j := 0) (by omega)
  have hRT0 : ⁅S5.uSub h.le L (P (2 * 0)), ZM _ (P (2 * 0 + b))⁆ ⊓
      Subgroup.centralizer (Qv _ (P (2 * 0 + 1)) : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (puTrans h.le L (P (2 * 0)) : Set (puAmalgam h.le).Universal) := by
    refine (hch.p2 hb hcase (j := 0) (by omega)).trans fun z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact commute_of_mem_stabCenter hz (puTrans_le_stab h.le L _ hy)
  obtain ⟨hlc, hJq⟩ := line54_of h54 h hmin hb2 hd hρ0 hadj0 hE0 hrel0 hRT0
  have hr1 := hch.r1_facts h32 hX2 h54 h59 hmin hd hb hcase hXU (i := 1) le_rfl (by omega)
  rw [show 2 * 1 + b = 2 * 0 + b + 2 by omega, show 2 * 1 - 2 + b = 2 * 0 + b by omega,
    show 2 * 1 - 2 = 2 * 0 by omega, show 2 * 1 - 1 = 2 * 0 + 1 by omega,
    show 2 * 1 = 2 * 0 + 2 by omega] at hr1
  obtain ⟨hL, hidx, hcard, hRle⟩ := hr1
  obtain ⟨hJR, -, hRZ⟩ := hch.localX_step h32 hX2 h54 h59 hmin hd hb hcase hXU hlc hJq
    (m := 0) (by omega)
  set Y := S5.uSub h.le L (P (2 * 0)) ⊓
    Subgroup.centralizer (ZM _ (P (2 * 0 + b)) : Set (puAmalgam h.le).Universal) with hY
  set A := critA _ (P (2 * 0 + 2)) (P (2 * 0 + b + 2)) with hA
  have hU0γ : S5.uSub h.le L (P (2 * 0 + 2)) ⊓
      Subgroup.centralizer (puTrans h.le L (P (2 * 0 + 2)) : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (P (2 * 0 + b + 2)) := by
    have := hch.uSub_inf_le_stabCenter_all h32 hX2 h54 h59 hmin hd hb hcase hXU hlc hJq
      (m := 1) (by omega) (1 + c) (by omega)
    rwa [show 2 * 1 = 2 * 0 + 2 by omega, show 2 * (1 + c) = 2 * 0 + b + 2 by omega] at this
  have hU0γ' : S5.uSub h.le L (P (2 * 0 + b + 2)) ⊓
      Subgroup.centralizer (puTrans h.le L (P (2 * 0 + b + 2)) : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (P (2 * 0 + 2)) := by
    have := hch.uSub_inf_le_stabCenter_all h32 hX2 h54 h59 hmin hd hb hcase hXU hlc hJq
      (m := 1 + c) (by omega) 1 (by omega)
    rwa [show 2 * 1 = 2 * 0 + 2 by omega, show 2 * (1 + c) = 2 * 0 + b + 2 by omega] at this
  have hcr : IsCritical _ (P (2 * 0 + 2)) (P (2 * 0 + b + 2)) := by
    have := hch.crit 1 (by omega)
    rwa [show 2 * 1 + b = 2 * 0 + b + 2 by omega, show 2 * 1 = 2 * 0 + 2 by omega] at this
  have hγM : IsMVtx _ (P (2 * 0 + 2)) := hcr.1
  have hγ'M : IsMVtx _ (P (2 * 0 + b + 2)) := hcr.isMVtx_right _ hyp
  have hcr' := ms22_iii _ hyp hb0 hC hcr
  have hZγst : ZM _ (P (2 * 0 + 2)) ≤ stab _ (P (2 * 0 + b + 2)) :=
    zm_le_stab_of_isCritical _ hyp hb0 hcr'
  have hZγ'st : ZM _ (P (2 * 0 + b + 2)) ≤ stab _ (P (2 * 0 + 2)) :=
    zm_le_stab_of_isCritical _ hyp hb0 hcr
  have hYst : Y ≤ stab _ (P (2 * 0 + b + 2)) :=
    (hch.uSub_inf_le_qv (m := 0) (by omega)).trans
      (qv_le_stab_of_adj _ (hch.adj_P (i := 2 * 0 + b + 1) (by omega)))
  have hAsup := (critA_le_of_relIndex h hd hXU hcr hidx).1
  have hR1U : ⁅Y, A⁆ ≤ S5.uSub h.le L (P (2 * 0 + b + 2)) := by
    rw [Subgroup.commutator_le]
    intro y hy x hx
    rw [commutatorElement_def]
    exact (liftX_gp h hd hγ'M (hYst hy) (hAsup hx)).1
  have hcRU' : critR _ (P (2 * 0 + 2)) (P (2 * 0 + b + 2)) ≤
      S5.uSub h.le L (P (2 * 0 + b + 2)) := by
    have := critR_le_uSub h hcr'
    rwa [critR, Subgroup.commutator_comm] at this
  have hcRU : critR _ (P (2 * 0 + 2)) (P (2 * 0 + b + 2)) ≤ S5.uSub h.le L (P (2 * 0 + 2)) :=
    critR_le_uSub h hcr
  have hcRst : critR _ (P (2 * 0 + 2)) (P (2 * 0 + b + 2)) ≤ stab _ (P (2 * 0 + b + 2)) :=
    hcRU'.trans ((S5B.uSub_le_zm h.le _).trans ((zm_le_qv_self _ hγ'M hb0).trans
      (qv_le_stab _ _)))
  have hR1cent : ⁅Y, A⁆ ≤
      Subgroup.centralizer (puTrans h.le L (P (2 * 0 + 2)) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.le_centralizer_iff]
    refine hL.trans (sup_le (Subgroup.le_centralizer_iff.1 hJR) ?_)
    refine (inf_le_left : S5.zHat _ _ _ ≤ ZM _ _).trans ?_
    rw [← Subgroup.le_centralizer_iff]
    exact hRZ.trans (zm_le_centralizer_zm hyp hb0 hγ'M)
  have hR1Z : ⁅Y, A⁆ ≤ stabCenter _ (P (2 * 0 + b + 2)) := by
    intro r₁ hr₁
    have h1 := hRle hr₁
    have hle : stabCenter _ (P (2 * 0 + b + 2)) ≤ Subgroup.normalizer
        (critR _ (P (2 * 0 + 2)) (P (2 * 0 + b + 2)) : Set (puAmalgam h.le).Universal) := by
      intro z hz
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun r hr => ?_)
      exact commute_of_mem_stabCenter hz (hcRst hr)
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at h1
    obtain ⟨r, hr, z, hz, rfl⟩ := h1
    have hzU : z ∈ S5.uSub h.le L (P (2 * 0 + b + 2)) := by
      have := mul_mem (inv_mem (hcRU' hr)) (hR1U hr₁)
      rwa [inv_mul_cancel_left] at this
    have hzL' : z ∈ Subgroup.centralizer
        (puTrans h.le L (P (2 * 0 + b + 2)) : Set (puAmalgam h.le).Universal) :=
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        commute_of_mem_stabCenter hz (puTrans_le_stab h.le L _ hy)
    have hzZ := hU0γ' ⟨hzU, hzL'⟩
    have hzL : z ∈ Subgroup.centralizer
        (puTrans h.le L (P (2 * 0 + 2)) : Set (puAmalgam h.le).Universal) :=
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        commute_of_mem_stabCenter hzZ (puTrans_le_stab h.le L _ hy)
    have hrL : r ∈ Subgroup.centralizer
        (puTrans h.le L (P (2 * 0 + 2)) : Set (puAmalgam h.le).Universal) := by
      have := mul_mem (hR1cent hr₁) (inv_mem hzL)
      rwa [mul_inv_cancel_right] at this
    exact mul_mem (hU0γ ⟨hcRU hr, hrL⟩) hz
  have hbot : ⁅Y, A⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro y hy x hx
    have hmem := hR1Z (Subgroup.commutator_mem_commutator hy hx)
    have hcL : ⁅y, x⁆ ∈ Subgroup.centralizer
        (puTrans h.le L (P (2 * 0 + b + 2)) : Set (puAmalgam h.le).Universal) :=
      Subgroup.mem_centralizer_iff.2 fun z hz =>
        commute_of_mem_stabCenter hmem (puTrans_le_stab h.le L _ hz)
    rw [commutatorElement_def] at hcL ⊢
    have h2 := (liftX_gp h hd hγ'M (hYst hy) (hAsup hx)).2 hcL
    rw [Subgroup.mem_bot, h2, mul_inv_cancel]
  rw [hbot, Subgroup.card_bot] at hcard
  have : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hd.1
  omega

end IsChain

end S510

end CFSG.Quasithin.MS93

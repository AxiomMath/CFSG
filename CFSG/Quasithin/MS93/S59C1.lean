module

public import CFSG.Quasithin.MS93.S59Set
public import CFSG.Quasithin.MS93.S59Crit
public import CFSG.Quasithin.MS93.S59L2

public noncomputable section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Pointwise

namespace S59

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Case1

theorem exists_mul_of_mem_hSub (h53 : S53) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    {x : (puAmalgam h.le).Universal} (hx : x ∈ hSub h.le L γ) :
    ∃ u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)), ∃ c ∈ stabCenter _ (baseA (puAmalgam h.le)),
      x = u * c := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨-, hQβ, -, hHX, -⟩ := hSub_facts h hb hd hβγ hγα hξ hξα hP
  have hxJ : x ∈ XM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) : Set (puAmalgam h.le).Universal) := by
    refine Subgroup.mem_inf.2 ⟨hHX hx, Subgroup.mem_centralizer_iff.2 fun j hj => ?_⟩
    exact (Subgroup.mem_centralizer_iff.1 (hQβ (S5B.jOff_le_qv h.le L _ _ _ hj)) x hx).symm
  have hxUD := h53 G M T L h hmin hb k F _ _ a hd hxJ
  have hDst : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.dSub h.le L (baseA _) : Set (puAmalgam h.le).Universal) := by
    refine le_normalizer_of_map_conj_le fun g hg => ?_
    rw [← S5B.dSub_smul h.le hLn, (mem_stab _).1 hg]
  have hUst : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) :=
    (S5B.uSub_le_zm h.le _).trans ((zm_le_qv_self _ hα h.critDist_pos).trans (qv_le_stab _ _))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUst.trans hDst)]
    at hxUD
  obtain ⟨u, hu, c, hcD, rfl⟩ := hxUD
  refine ⟨u, hu, c, ?_, rfl⟩
  have hUX : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ XM _ (baseA (puAmalgam h.le)) :=
    (S5B.uSub_le_zm h.le _).trans (zm_le_xm _ h.hyp20 h.critDist_pos hα)
  have hcX : c ∈ XM _ (baseA (puAmalgam h.le)) := by
    have := mul_mem (inv_mem (hUX hu)) (hHX hx)
    simpa using this
  have hUc : ∀ y ∈ S5.uSub h.le L (baseA (puAmalgam h.le)), u * y = y * u := fun y hy =>
    Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ h.hyp20 hα
      (S5B.uSub_le_zm h.le _ hy)) u (zm_le_qv_self _ hα h.critDist_pos (S5B.uSub_le_zm h.le _ hu))
  have hcT : c ∈ Subgroup.centralizer (Qv _ (baseB (puAmalgam h.le)) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htα : t ∈ stab _ (baseA (puAmalgam h.le)) := qv_le_stab_of_adj _ hαβ.symm ht
    have htx := Subgroup.mem_centralizer_iff.1 (hQβ ht) (u * c) hx
    have hu' : t * u * t⁻¹ ∈ S5.uSub h.le L (baseA (puAmalgam h.le)) :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_uSub h _ htα) u).1 hu
    have hc' : t * c * t⁻¹ ∈ S5.dSub h.le L (baseA (puAmalgam h.le)) :=
      (Subgroup.mem_normalizer_iff.1 (hDst htα) c).1 hcD
    have e1 : u⁻¹ * (t * u * t⁻¹) = c * (t * c * t⁻¹)⁻¹ := by
      have e2 : t * (u * c) * t⁻¹ = u * c := by rw [← htx, mul_inv_cancel_right]
      calc u⁻¹ * (t * u * t⁻¹) = u⁻¹ * (t * (u * c) * t⁻¹) * (t * c * t⁻¹)⁻¹ := by group
        _ = u⁻¹ * (u * c) * (t * c * t⁻¹)⁻¹ := by rw [e2]
        _ = c * (t * c * t⁻¹)⁻¹ := by group
    have hD : t * u * t⁻¹ * u⁻¹ ∈ S5.dSub h.le L (baseA (puAmalgam h.le)) := by
      have e3 : t * u * t⁻¹ * u⁻¹ = u⁻¹ * (t * u * t⁻¹) := by
        have := hUc _ hu'
        calc t * u * t⁻¹ * u⁻¹ = u⁻¹ * (u * (t * u * t⁻¹)) * u⁻¹ := by group
          _ = u⁻¹ * ((t * u * t⁻¹) * u) * u⁻¹ := by rw [this]
          _ = u⁻¹ * (t * u * t⁻¹) := by group
      rw [e3, e1]
      exact mul_mem hcD (inv_mem hc')
    have hlift := lift_baseA h hd htα hu (Subgroup.mem_inf.1 hD).2
    have htu : t * u = u * t := by
      calc t * u = t * u * t⁻¹ * t := by group
        _ = u * t := by rw [hlift]
    calc t * c = u⁻¹ * (t * u * c) := by rw [htu]; group
      _ = u⁻¹ * (u * c * t) := by rw [mul_assoc t u c, ← htx, mul_assoc]
      _ = c * t := by group
  exact S5Q2.xm_inf_centralizer_inf_centralizer_qv_le h hd hα hαβ
    ⟨⟨hcX, (Subgroup.mem_inf.1 hcD).2⟩, hcT⟩

theorem commutator_gen_eq_bot (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) {γ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    {Z : Subgroup (puAmalgam h.le).Universal}
    (hZc : ∀ y ∈ hSub h.le L γ, (∀ z ∈ Z, z * y = y * z) →
      y ∈ stabCenter _ (baseA (puAmalgam h.le)))
    (hbb : ∀ t ∈ tZero h.le L γ,
      (∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) →
        ∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ γ)
    {N : Subgroup (puAmalgam h.le).Universal} (hNT : N ≤ tZero h.le L γ)
    {x : (puAmalgam h.le).Universal} (hx : x ∈ stab _ (baseA (puAmalgam h.le)))
    (hxH : x ∈ Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal))
    (hN : ⁅ZM _ (x • γ), N⁆ ≤ Subgroup.centralizer (Z : Set (puAmalgam h.le).Universal)) :
    ⁅ZM _ (x • γ), N⁆ = ⊥ := by
  obtain ⟨hγ, -, -⟩ := gamma_facts h hβγ hγα
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hxα : x • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hx
  have hνM : IsMVtx _ (x • γ) := (isMVtx_smul _ x γ).2 hγ
  have hxβ : (puAmalgam h.le).treeGraph.Adj (baseA _) (x • baseB (puAmalgam h.le)) := by
    have := (adj_smul _ x _ _).2 hαβ
    rwa [hxα] at this
  have hβν : (puAmalgam h.le).treeGraph.Adj (x • baseB (puAmalgam h.le)) (x • γ) :=
    (adj_smul _ x _ _).2 hβγ
  have hNQ : N ≤ Qv _ (x • baseB (puAmalgam h.le)) :=
    hNT.trans ((tZero_le_qv h.le γ).trans (qv_le_qv _ h.hyp20 hα hxβ))
  have hNst : N ≤ stab _ (x • γ) := hNQ.trans (qv_le_stab_of_adj _ hβν)
  have hHx : (hSub h.le L γ).map (MulAut.conj x).toMonoidHom = hSub h.le L γ := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      have hcz := Subgroup.mem_centralizer_iff.1 hxH z hz
      show x * z * x⁻¹ ∈ _
      rw [← hcz, mul_inv_cancel_right]
      exact hz
    · intro z hz
      refine ⟨z, hz, ?_⟩
      have hcz := Subgroup.mem_centralizer_iff.1 hxH z hz
      show x * z * x⁻¹ = z
      rw [← hcz, mul_inv_cancel_right]
  have hZN : ⁅ZM _ (x • γ), N⁆ ≤ hSub h.le L γ := by
    rw [← hHx, ← commutator_zm_tZero_smul h hb hβγ hx]
    exact Subgroup.commutator_mono le_rfl hNT
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hUx := S5B.uSub_smul h.le hLn x γ
  have hTn := le_normalizer_tZero h hb (L := L) hαβ hβγ
  have hUNα : ⁅S5.uSub h.le L (x • γ), N⁆ ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
    intro y hy
    have hyZ : y ∈ ⁅ZM _ (x • γ), N⁆ :=
      Subgroup.commutator_mono (S5B.uSub_le_zm h.le (x • γ)) le_rfl hy
    exact hZc y (hZN hyZ) fun z hz => Subgroup.mem_centralizer_iff.1 (hN hyZ) z hz
  have hUN : ⁅S5.uSub h.le L (x • γ), N⁆ ≤
      Subgroup.centralizer (puTrans h.le L (x • γ) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.commutator_le]
    intro u hu t ht
    have ht₀ : x⁻¹ * t * x ∈ tZero h.le L γ := by
      have := (Subgroup.mem_normalizer_iff.1 (hTn (inv_mem hx)) t).1 (hNT ht)
      rwa [inv_inv] at this
    have hall : ∀ u' ∈ S5.uSub h.le L γ,
        ⁅u', x⁻¹ * t * x⁆ ∈ stabCenter _ (baseA (puAmalgam h.le)) := by
      intro u' hu'
      have hxu' : x * u' * x⁻¹ ∈ S5.uSub h.le L (x • γ) := by
        rw [hUx]
        exact ⟨u', hu', rfl⟩
      have hc := hUNα (Subgroup.commutator_mem_commutator hxu' ht)
      have e : ⁅u', x⁻¹ * t * x⁆ = x⁻¹ * ⁅x * u' * x⁻¹, t⁆ * x := by
        simp only [commutatorElement_def]
        group
      rw [e, (S510.mem_stabCenter_iff.1 hc).2 x⁻¹ (inv_mem hx), inv_mul_cancel_right]
      exact hc
    rw [hUx] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    have hγc := hbb _ ht₀ hall u₀ hu₀
    have hyν : ⁅(MulAut.conj x).toMonoidHom u₀, t⁆ ∈ stabCenter _ (x • γ) := by
      rw [S510.stabCenter_smul]
      refine ⟨⁅u₀, x⁻¹ * t * x⁆, hγc, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (S510.mem_stabCenter_iff.1 hyν).2 l (puTrans_le_stab h.le L _ hl)
  have hUN' := commutator_eq_bot_of_le h hd hνM hNst hUN
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, S5B.zm_eq_zh_sup_uSub h hνM hβν.symm]
  refine sup_le ?_ (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hUN')
  rw [Subgroup.le_centralizer_iff]
  exact hNQ.trans (Subgroup.le_centralizer_iff.1 (zh_le_centralizer _ _))

theorem case1_core (h32 : S32) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    (hbb : ∀ t ∈ tZero h.le L γ,
      (∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) →
        ∀ u ∈ S5.uSub h.le L γ, ⁅u, t⁆ ∈ stabCenter _ γ)
    {K : Subgroup (puAmalgam h.le).Universal} (hKst : K ≤ stab _ (baseA (puAmalgam h.le)))
    (hKH : K ≤ Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal))
    {α'' : Vtx (puAmalgam h.le)} (hc'' : IsCritical _ (baseA (puAmalgam h.le)) α'')
    {m : (puAmalgam h.le).Universal} (hm : m ∈ stab _ (baseA (puAmalgam h.le)))
    (hγ'' : geo _ (baseA (puAmalgam h.le)) α'' 2 = m • γ)
    (hgen : K ⊔ S5.zHat _ (baseA (puAmalgam h.le)) α'' = stab _ (baseA (puAmalgam h.le))) :
    False := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hyp := h.hyp20
  have hC := h.centHyp
  have h32' := (h32 G M T L h).2.1
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  obtain ⟨hγ, hd2, -⟩ := gamma_facts h hβγ hγα
  obtain ⟨hHU, -, -, -, -⟩ := hSub_facts h hb' hd hβγ hγα hξ hξα hP
  have hUγB := uSub_not_le_bSub_of_hyp h hb' hd hβγ hγα hξ hξα hP
  have hγα' : (puAmalgam h.le).treeGraph.dist γ (baseA _) < critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, hd2]
    exact hb'
  have hHst : hSub h.le L γ ≤ stab _ (baseA (puAmalgam h.le)) :=
    hHU.trans ((S5B.uSub_le_zm h.le γ).trans ((zm_le_qv_of_dist_lt _ hγ hγα').trans
      (qv_le_stab _ _)))
  obtain ⟨-, -, hZ''st, hRX, hXX, -⟩ := S5B.crit_facts h hc''
  have hZcen : ∀ y ∈ hSub h.le L γ,
      (∀ z ∈ S5.zHat _ (baseA (puAmalgam h.le)) α'', z * y = y * z) →
      y ∈ stabCenter _ (baseA (puAmalgam h.le)) := by
    intro y hy hyZ
    rw [S510.mem_stabCenter_iff]
    refine ⟨hHst hy, fun g hg => ?_⟩
    have hle : K ⊔ S5.zHat _ (baseA (puAmalgam h.le)) α'' ≤
        Subgroup.centralizer ({y} : Set (puAmalgam h.le).Universal) := by
      refine sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 (hKH hx) y hy).symm) fun z hz =>
          Subgroup.mem_centralizer_singleton_iff.2 (hyZ z hz)
    rw [hgen] at hle
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
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
  have hkill : ∀ {N : Subgroup (puAmalgam h.le).Universal}, N ≤ tZero h.le L γ →
      (∀ x ∈ K, ⁅ZM _ (x • γ), N⁆ ≤
        Subgroup.centralizer (S5.zHat _ (baseA (puAmalgam h.le)) α'' : Set _)) →
      W ≤ Subgroup.centralizer (N : Set (puAmalgam h.le).Universal) := by
    intro N hNT hN
    refine hWle fun x hx => ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact commutator_gen_eq_bot h hb' hd hβγ hγα hZcen hbb hNT (hKst hx) (hKH hx) (hN x hx)
  have hdd'' : (puAmalgam h.le).treeGraph.dist (baseA _) α'' = critDist (puAmalgam h.le) :=
    hc''.2.1
  obtain ⟨m₀, hm₀⟩ := ms21_v _ hyp
  have hα''M : IsMVtx _ α'' := hc''.isMVtx_right _ hyp
  set σ₂ := geo _ α'' (baseA (puAmalgam h.le)) 2 with hσ₂def
  set σ₁ := geo _ α'' (baseA (puAmalgam h.le)) 1 with hσ₁def
  have hdα''σ₂ : (puAmalgam h.le).treeGraph.dist α'' σ₂ = 2 :=
    dist_geo _ (by rw [SimpleGraph.dist_comm, hdd'']; omega)
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
  have hQα''Z : Qv _ α'' ≤
      Subgroup.centralizer (S5.zHat _ (baseA (puAmalgam h.le)) α'' : Set _) :=
    (Subgroup.le_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα''M)).trans
      (Subgroup.centralizer_le inf_le_left)
  have hσ₂T : ZM _ σ₂ ≤ tZero h.le L γ :=
    zm_le_tZero h hb' hαβ hβγ hσ₂M (by rw [SimpleGraph.dist_comm, hdσ₂α]; omega)
      (by rw [SimpleGraph.dist_comm, hdσ₂α]; omega)
  have hW1 : W ≤ Subgroup.centralizer (ZM _ σ₂ : Set (puAmalgam h.le).Universal) := by
    refine hkill hσ₂T fun x hx => ?_
    have hle : (puAmalgam h.le).treeGraph.dist (x • γ) σ₂ ≤ critDist (puAmalgam h.le) := by
      have t := dist_triangle _ (x • γ) (baseA (puAmalgam h.le)) σ₂
      rw [SimpleGraph.dist_comm (u := x • γ) (v := baseA _), hdist x hx,
        SimpleGraph.dist_comm (u := baseA _) (v := σ₂), hdσ₂α] at t
      omega
    have hst := zm_le_stab_of_dist_le h ((isMVtx_smul _ x γ).2 hγ) hle
    rw [Subgroup.commutator_comm]
    exact (commutator_le_left_of_le_normalizer (hst.trans (stab_le_normalizer_zm _ _))).trans
      ((zm_le_qv_of_dist_lt _ hσ₂M (by rw [SimpleGraph.dist_comm, hdα''σ₂]; omega)).trans
        hQα''Z)
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
  have hAT : critA _ (baseA (puAmalgam h.le)) α'' ≤ tZero h.le L γ := by
    rw [← tZero_smul_eq h hb' hαβ hβγ hm]
    refine xm_inf_le_tZero h ((isMVtx_smul _ m γ).2 hγ) ?_
    rw [← hγ'', dist_geo_right _ (by omega), hdd'']
    omega
  have hW2 : W ≤ Subgroup.centralizer (critA _ (baseA (puAmalgam h.le)) α'' : Set _) := by
    refine hkill hAT fun x hx => ?_
    have hst : ZM _ (x • γ) ≤ stab _ α'' := (hgenW x hx).trans hWst''
    rw [Subgroup.commutator_comm]
    exact ((Subgroup.commutator_mono inf_le_left le_rfl).trans
      (commutator_le_left_of_le_normalizer (hst.trans (stab_le_normalizer_xm _ _)))).trans
      ((xm_le_centralizer _ α'').trans (Subgroup.centralizer_le
        (inf_le_left.trans (zm_le_qv_self _ hα''M hb0))))
  have hWQα : W ≤ Qv _ (baseA (puAmalgam h.le)) :=
    hWle fun x hx => zm_le_qv_of_dist_lt _ ((isMVtx_smul _ x γ).2 hγ)
      (by rw [SimpleGraph.dist_comm, hdist x hx]; exact hb')
  have hYR : W ≤ Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α'' : Set _) :=
    hWQα.trans ((qv_le_centralizer_xm _ _).trans (Subgroup.centralizer_le hRX))
  have hAY : ⁅critA _ (baseA (puAmalgam h.le)) α'', W⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hW2
  have hcomm := S5B.commutator_zHat_le' h hd hc'' hWT hYR hAY
  have hWZX : ⁅W, S5.zHat _ (baseA (puAmalgam h.le)) α''⁆ ≤ XM _ (baseA (puAmalgam h.le)) :=
    hcomm.trans (sup_le hXX hRX)
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
  obtain ⟨y₀, hy₀Z, hy₀st, hy₀2, hy₀Q⟩ := exists_zHat_not_mem h55 h56 h hmin hb' hd hc''
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
  have hB := inf_le_bSub_of_elt h h32' hα (sup_le hWst ((xm_le_qv _ _).trans (qv_le_stab _ _)))
    ((puTrans_le_stab h.le L _).trans hPn) hy₀st hy₀2 hy₀Q hPy
  have hZγW : ZM _ γ ≤ W := by
    have := hgenW 1 (one_mem K)
    rwa [one_smul] at this
  exact hUγB (le_trans (le_inf ((S5B.uSub_le_zm h.le γ).trans (hZγW.trans le_sup_left))
    ((S5B.uSub_le_zm h.le γ).trans (S5B.zm_le_vv_of_dist hγ hd2.le))) hB)


theorem case1_false (h32 : S32) (h53 : S53) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ' : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {ξ : Vtx (puAmalgam h.le)}
    (hξ : IsCritical _ ξ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤ 2 ^ k)
    (hnc : ¬ hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      stabCenter _ (baseA (puAmalgam h.le)))
    (ha : ∃ h₁ ∈ hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
      stab _ (baseA (puAmalgam h.le)) ⊓
          Subgroup.centralizer ({h₁} : Set (puAmalgam h.le).Universal) ≤
        Subgroup.centralizer
          (hSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2) : Set (puAmalgam h.le).Universal))
    (hbb : ∀ t ∈ tZero h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
      (∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
        ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) →
        ∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
          ⁅u, t⁆ ∈ stabCenter _ (geo _ (baseA (puAmalgam h.le)) α' 2)) : False := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 := h.critDist_pos
  have hyp := h.hyp20
  have hC := h.centHyp
  have h32' := (h32 G M T L h).2.1
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
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
  obtain ⟨hγ, -, -⟩ := gamma_facts h hβγ hγα
  obtain ⟨hHU, -, -, -, -⟩ := hSub_facts h hb' hd hβγ hγα hξ hξα hP
  have hUγB := uSub_not_le_bSub_of_hyp h hb' hd hβγ hγα hξ hξα hP
  have hγα' : (puAmalgam h.le).treeGraph.dist γ (baseA _) < critDist (puAmalgam h.le) := by
    rw [SimpleGraph.dist_comm, hd2]
    exact hb'
  have hHst : hSub h.le L γ ≤ stab _ (baseA (puAmalgam h.le)) :=
    hHU.trans ((S5B.uSub_le_zm h.le γ).trans ((zm_le_qv_of_dist_lt _ hγ hγα').trans
      (qv_le_stab _ _)))
  obtain ⟨h₁, hh₁, hK⟩ := ha
  have hh₁c : h₁ ∉ stabCenter _ (baseA (puAmalgam h.le)) := by
    intro hc1
    apply hnc
    intro y hy
    rw [S510.mem_stabCenter_iff]
    refine ⟨hHst hy, fun g hg => ?_⟩
    have hg' : g ∈ stab _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer ({h₁} : Set (puAmalgam h.le).Universal) :=
      ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 ((S510.mem_stabCenter_iff.1 hc1).2 g hg)⟩
    exact (Subgroup.mem_centralizer_iff.1 (hK hg') y hy).symm
  obtain ⟨u₁, hu₁, d₁, hd₁, rfl⟩ :=
    exists_mul_of_mem_hSub h53 h hmin hb' hd hβγ hγα hξ hξα hP hh₁
  have hu₁L : u₁ ∉
      Subgroup.centralizer (puTrans h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    fun hL => hh₁c (mul_mem (uSub_inf_le_stabCenter h hd hα ⟨hu₁, hL⟩) hd₁)
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
  obtain ⟨m, hm, e, he, hne⟩ := exists_conj_not_comm h hd hα hu₁ hu₁L hZ'st hZ'2
    (zHat_not_le_qv_baseA h55 h56 h hmin hb' hd hc)
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
    exact centralizer_sup_eq h hd hα hu₁ hu₁L hZ''st hZ''2 he'' hne''
  have hγ'' : geo _ (baseA (puAmalgam h.le)) α'' 2 = m⁻¹ • γ := by
    have := geo_smul _ m⁻¹ (baseA (puAmalgam h.le)) α' 2
    rw [hmα] at this
    exact this
  exact case1_core h32 h55 h56 h hmin hb hd hβγ hγα hξ hξα hP hbb inf_le_left hK hc''
    (inv_mem hm) hγ'' hgen

theorem case1_false_of_gen (h32 : S32) (h55 : S55) (h56 : S56)
    (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 4 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hαβ' : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) {ξ : Vtx (puAmalgam h.le)}
    (hξ : IsCritical _ ξ (geo _ (baseA (puAmalgam h.le)) α' 2))
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex
      (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2)) ≤ 2 ^ k)
    (hbb : ∀ t ∈ tZero h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
      (∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
        ⁅u, t⁆ ∈ stabCenter _ (baseA (puAmalgam h.le))) →
        ∀ u ∈ S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2),
          ⁅u, t⁆ ∈ stabCenter _ (geo _ (baseA (puAmalgam h.le)) α' 2))
    {g : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hgen : Qv _ (g⁻¹ • baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA (puAmalgam h.le)) α' =
      stab _ (baseA (puAmalgam h.le))) : False := by
  have hb' : 2 < critDist (puAmalgam h.le) := by omega
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
  obtain ⟨-, hQβ, -, -, -⟩ := hSub_facts h hb' hd hβγ hγα hξ hξα hP
  have hgα : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).1 hg
  have hc'' : IsCritical _ (baseA (puAmalgam h.le)) (g • α') := by
    have := (isCritical_smul _ g _ _).2 hc
    rwa [hgα] at this
  have hγ'' : geo _ (baseA (puAmalgam h.le)) (g • α') 2 = g • γ := by
    have := geo_smul _ g (baseA (puAmalgam h.le)) α' 2
    rw [hgα] at this
    exact this
  have hgen' : Qv _ (baseB (puAmalgam h.le)) ⊔ S5.zHat _ (baseA (puAmalgam h.le)) (g • α') =
      stab _ (baseA (puAmalgam h.le)) := by
    have e1 : Qv _ (baseB (puAmalgam h.le)) =
        (Qv _ (g⁻¹ • baseB (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom := by
      rw [← qv_smul, smul_inv_smul]
    have e2 : S5.zHat _ (baseA (puAmalgam h.le)) (g • α') =
        (S5.zHat _ (baseA (puAmalgam h.le)) α').map (MulAut.conj g).toMonoidHom := by
      have := S5B.zHat_smul _ g (baseA (puAmalgam h.le)) α'
      rwa [hgα] at this
    have e3 : stab _ (baseA (puAmalgam h.le)) =
        (stab _ (baseA (puAmalgam h.le))).map (MulAut.conj g).toMonoidHom := by
      rw [← stab_smul, hgα]
    rw [e1, e2, ← Subgroup.map_sup, hgen, ← e3]
  exact case1_core h32 h55 h56 h hmin hb hd hβγ hγα hξ hξα hP hbb
    (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm) hQβ hc'' hg hγ'' hgen'

theorem finite_commutator_uSub (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {E : Subgroup (puAmalgam h.le).Universal} (hE : E ≤ stab _ δ) :
    Finite ↥⁅S5.uSub h.le L δ, E⁆ := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  obtain ⟨E₀, hE₀M, rfl⟩ := S5B.exists_eq_map_imM h.le g hE
  apply Nat.finite_of_card_ne_zero
  rw [commutator_uSub_conj_eq h g hE₀M, S5B.card_map_conj,
    S5B.card_imM h.le (commutator_le_of_le (Uq_le h.L_le) hE₀M)]
  exact Nat.card_pos.ne'

theorem case1_ab_of_two (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hd : S5.IsSp4Data M T L k F a) (hk : k = 1) {γ ξ : Vtx (puAmalgam h.le)}
    (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ) (hγα : γ ≠ baseA _)
    (hξ : IsCritical _ ξ γ)
    (hξα : (puAmalgam h.le).treeGraph.dist ξ (baseA _) + 2 = critDist (puAmalgam h.le))
    (hP : (S5.bSub h.le L (baseA _)).relIndex (S5.uSub h.le L γ) ≤ 2 ^ k)
    (hnc : ¬ hSub h.le L γ ≤ stabCenter _ (baseA (puAmalgam h.le))) :
    (∃ h₁ ∈ hSub h.le L γ, stab _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer ({h₁} : Set (puAmalgam h.le).Universal) ≤
      Subgroup.centralizer (hSub h.le L γ : Set (puAmalgam h.le).Universal)) ∧
      hSub h.le L γ ⊓ stabCenter _ (baseA (puAmalgam h.le)) ≤ stabCenter _ γ := by
  obtain ⟨hγ, -, -⟩ := gamma_facts h hβγ hγα
  obtain ⟨-, hTst, -, -, hrel⟩ := tZero_facts h hb hd hβγ hγα hξ hξα hP
  have hcard : Nat.card ↥(hSub h.le L γ) ≤ 2 := card_commutator_le_two h hd hk hγ hTst hrel
  obtain ⟨h₁, hh₁, hh₁c⟩ := Set.not_subset.1 hnc
  have hh₁1 : h₁ ≠ 1 := by
    rintro rfl
    exact hh₁c (one_mem _)
  have hfin : Finite ↥(hSub h.le L γ) := finite_commutator_uSub h hγ hTst
  have hcard2 : Nat.card ↥(hSub h.le L γ) = 2 := by
    have h2 : 1 < Nat.card ↥(hSub h.le L γ) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 fun hbot =>
        hh₁1 (Subgroup.mem_bot.1 (hbot ▸ hh₁))
    omega
  have hmem : ∀ y ∈ hSub h.le L γ, y = 1 ∨ y = h₁ := fun y hy =>
    eq_one_or_eq_of_card_two hcard2 hy hh₁ hh₁1
  refine ⟨⟨h₁, hh₁, fun g hg => ?_⟩, fun y hy => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hmem y hy with rfl | rfl
    · group
    · exact (Subgroup.mem_centralizer_singleton_iff.1 hg.2).symm
  · rcases hmem y hy.1 with rfl | rfl
    · exact one_mem _
    · exact absurd hy.2 hh₁c

end Case1

end S59

end CFSG.Quasithin.MS93

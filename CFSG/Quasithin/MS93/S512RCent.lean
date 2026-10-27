module

public import CFSG.Quasithin.MS93.S512NR2C
public import CFSG.Quasithin.MS93.S51Main
public import CFSG.Quasithin.MS93.S5B56R
public import CFSG.Quasithin.MS93.S5B57

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512R

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem mem_dSub_of_comm_jOff (h51 : S51) (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    (hpu : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) {l : Submodule F (MSP.V4 F)}
    (hl : MSP.IsLine l)
    (hJl : S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hgen : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a (MSP.qLine l) →
      IsPGroup 2 E → (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E →
      S5.rconj y E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _))
    {r : (puAmalgam h.le).Universal}
    (hr : r ∈ S5.uSub h.le L (baseA _) ⊔ S5.dSub h.le L (baseA _))
    (hrJ : ∀ t ∈ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _), t * r * t⁻¹ = r)
    (hry : ∀ t ∈ S5.rconj y (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)), t * r * t⁻¹ = r) :
    r ∈ S5.dSub h.le L (baseA _) := by
  have := hd.charP
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hDn : stab _ (baseA (puAmalgam h.le)) ≤
      Subgroup.normalizer (S5.dSub h.le L (baseA _) : Set (puAmalgam h.le).Universal) :=
    S310.le_normalizer_inf (stab_le_normalizer_qv _ _)
      (le_normalizer_centralizer (stab_le_normalizer_puTrans h.le hLn _))
  have hUst : S5.uSub h.le L (baseA (puAmalgam h.le)) ≤ stab _ (baseA (puAmalgam h.le)) := by
    rw [S5.uSub_baseA h, puAmalgam.stab_baseA]
    exact imM_mono h.le (Uq_le h.L_le)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hUst.trans hDn)] at hr
  obtain ⟨u, hu, d, hdD, rfl⟩ := hr
  have key : ∀ t ∈ stab _ (baseA (puAmalgam h.le)), t * (u * d) * t⁻¹ = u * d →
      u⁻¹ * (t * u * t⁻¹) ∈ S5.dSub h.le L (baseA _) := by
    intro t ht htr
    have e1 : t * u * t⁻¹ * (t * d * t⁻¹) = u * d := by
      rw [← htr]
      group
    have e : u⁻¹ * (t * u * t⁻¹) = d * (t * d * t⁻¹)⁻¹ := by
      calc u⁻¹ * (t * u * t⁻¹) = u⁻¹ * (t * u * t⁻¹ * (t * d * t⁻¹)) * (t * d * t⁻¹)⁻¹ := by
            group
        _ = u⁻¹ * (u * d) * (t * d * t⁻¹)⁻¹ := by rw [e1]
        _ = d * (t * d * t⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem hdD (inv_mem ((Subgroup.mem_normalizer_iff.1 (hDn ht) d).1 hdD))
  rw [S5.uSub_baseA h] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  have hu₀U : (u₀ : G) ∈ Uq M T L := Subgroup.mem_subgroupOf.1 hu₀
  set w := nv.vec ⟨u₀, hu₀U⟩ with hw
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hfix : ∀ t₀ : ↥M, (puAmalgam h.le).ofA t₀ * ((puAmalgam h.le).ofA u₀ * d) *
      ((puAmalgam h.le).ofA t₀)⁻¹ = (puAmalgam h.le).ofA u₀ * d →
      MSP.mat (a t₀) *ᵥ w = w := by
    intro t₀ ht₀
    have h1 := key _ (S512N.ofA_mem_stab_baseA h.le t₀) ht₀
    rw [S5.dSub_baseA h, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
      S512N.ofA_mem_imM_iff] at h1
    have htu : (t₀ : G) * u₀ * (t₀ : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn t₀.2) u₀).1 hu₀U
    have h3 : (((⟨u₀, hu₀U⟩ : ↥(Uq M T L))⁻¹ * ⟨_, htu⟩ : ↥(Uq M T L)) : G) ∈
        Subgroup.centralizer (L : Set G) := h1.2
    have h4 := (nv.vec_eq_zero_iff _).2 h3
    rw [S5.NatVec.vec_mul, S5.NatVec.vec_inv, S5.NatVec.vec_conj nv t₀ ⟨u₀, hu₀U⟩ htu] at h4
    rw [hw]
    exact (neg_add_eq_zero.1 h4).symm
  have hJM : S5.jOffM M T L (2 ^ k) ≤ M := iSup₂_le fun E hE => (S5.offSetM_le _ hE).trans h.le
  have hJl' : S5.imSp a (S5.jOffM M T L (2 ^ k)) ≤ MSP.qLine l := by
    rintro _ ⟨j, hj, rfl⟩
    have h1 : (puAmalgam h.le).ofA j ∈ S5.vPre h.le a (MSP.qLine l) := by
      apply hJl
      rw [S5.jOff_baseA h]
      exact ⟨j, hj, rfl⟩
    obtain ⟨m, hm, hmj⟩ := h1
    rw [(puAmalgam h.le).ofA_injective hmj] at hm
    exact hm
  have hCl : MSP.fixSp (S5.imSp a (S5.jOffM M T L (2 ^ k))) = l :=
    S5.fixSp_eq_of_le_qLine hl hJl' (S512N.card_lt_card_imSp_jOffM h51 hd h hpu hb)
  have hJα : ∀ j : ↥M, (j : G) ∈ S5.jOffM M T L (2 ^ k) →
      (puAmalgam h.le).ofA j ∈ S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) := fun j hj => by
    rw [S5.jOff_baseA h]
    exact ⟨j, Subgroup.mem_subgroupOf.2 hj, rfl⟩
  have hwl : w ∈ l := by
    rw [← hCl, MSP.mem_fixSp]
    rintro _ ⟨j, hj, rfl⟩
    exact hfix j (hrJ _ (hJα j (Subgroup.mem_subgroupOf.1 hj)))
  rw [puAmalgam.stab_baseA] at hy
  obtain ⟨y₀, -, rfl⟩ := hy
  have hywl : MSP.mat (a y₀) *ᵥ w ∈ l := by
    rw [← hCl, MSP.mem_fixSp]
    rintro _ ⟨j, hj, rfl⟩
    have e : (puAmalgam h.le).ofA y₀ * (puAmalgam h.le).ofA (y₀⁻¹ * j * y₀) *
        ((puAmalgam h.le).ofA y₀)⁻¹ = (puAmalgam h.le).ofA j := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      group
    have hmem : (puAmalgam h.le).ofA (y₀⁻¹ * j * y₀) ∈
        S5.rconj ((puAmalgam h.le).ofA y₀) (S5.jOff h.le L (2 ^ k) (baseA _) (baseB _)) := by
      rw [S5.mem_rconj, e]
      exact hJα j (Subgroup.mem_subgroupOf.1 hj)
    have h1 := hfix _ (hry _ hmem)
    have e3 : a (y₀⁻¹ * j * y₀) = (a y₀)⁻¹ * a j * a y₀ := by simp [map_mul, map_inv]
    rw [e3] at h1
    calc MSP.mat (a j) *ᵥ (MSP.mat (a y₀) *ᵥ w) =
        MSP.mat (a y₀) *ᵥ (MSP.mat ((a y₀)⁻¹ * a j * a y₀) *ᵥ w) := by
          rw [← MSP.mat_mul_mulVec, ← MSP.mat_mul_mulVec]
          congr 2
          group
      _ = MSP.mat (a y₀) *ᵥ w := by rw [h1]
  obtain ⟨hl2, hlc⟩ := S5C56.isPGroup_qLine hd hl
  obtain ⟨E, hEle, hE2, hEim⟩ := S5C56.exists_isPGroup_vIm_eq h hd hl2
  have hEst : E ≤ stab _ (baseA (puAmalgam h.le)) := hEle.trans (S5.vPre_le_stab h _)
  have hErel : (Qv _ (baseA (puAmalgam h.le))).relIndex E = (2 ^ k) ^ 3 := by
    rw [← S5.card_vIm h hd hEst hE2, hEim, hlc]
  have hlt : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
    rw [hErel]
    exact Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by have := hd.1; omega)) (by norm_num)
  have hst := hgen E hEle hE2 hlt
  set Fx : Subgroup ↥M := (MSP.fixer (F ∙ w)).comap a with hFx
  have hmemFx : ∀ m : ↥M, m ∈ Fx ↔ MSP.mat (a m) *ᵥ w = w := by
    intro m
    rw [hFx, Subgroup.mem_comap, MSP.mem_fixer]
    constructor
    · intro h1
      exact h1 w (Submodule.mem_span_singleton_self w)
    · intro h1 v hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
      rw [Matrix.mulVec_smul, h1]
  have hle : stab _ (baseA (puAmalgam h.le)) ≤ Fx.map (puAmalgam h.le).ofA := by
    rw [← hst]
    refine sup_le (sup_le ?_ ?_) ?_
    · intro e he
      have heα : e ∈ stab _ (baseA (puAmalgam h.le)) := by
        have h1 := hEst ((S5.mem_rconj).1 he)
        have e2 : e = ((puAmalgam h.le).ofA y₀)⁻¹ *
            ((puAmalgam h.le).ofA y₀ * e * ((puAmalgam h.le).ofA y₀)⁻¹) *
            (puAmalgam h.le).ofA y₀ := by group
        rw [e2]
        exact mul_mem (mul_mem (inv_mem (S512N.ofA_mem_stab_baseA h.le y₀)) h1)
          (S512N.ofA_mem_stab_baseA h.le y₀)
      rw [puAmalgam.stab_baseA] at heα
      obtain ⟨m, -, rfl⟩ := heα
      refine ⟨m, (hmemFx m).2 ?_, rfl⟩
      have h1 := hEle ((S5.mem_rconj).1 he)
      have e4 : (puAmalgam h.le).ofA y₀ * (puAmalgam h.le).ofA m *
          ((puAmalgam h.le).ofA y₀)⁻¹ = (puAmalgam h.le).ofA (y₀ * m * y₀⁻¹) := by
        simp [map_mul, map_inv]
      rw [e4] at h1
      obtain ⟨m', hm', hm'e⟩ := h1
      rw [(puAmalgam h.le).ofA_injective hm'e] at hm'
      have h2 := (MSP.mem_fixer.1 hm') _ hywl
      have e5 : a (y₀ * m * y₀⁻¹) = a y₀ * a m * (a y₀)⁻¹ := by simp [map_mul, map_inv]
      rw [e5] at h2
      have h3 : MSP.mat (a m) *ᵥ w = MSP.mat (a y₀)⁻¹ *ᵥ
          (MSP.mat (a y₀ * a m * (a y₀)⁻¹) *ᵥ (MSP.mat (a y₀) *ᵥ w)) := by
        rw [← MSP.mat_mul_mulVec, ← MSP.mat_mul_mulVec]
        congr 2
        group
      rw [h3, h2, ← MSP.mat_mul_mulVec, inv_mul_cancel, MSP.mat_one, Matrix.one_mulVec]
    · intro e he
      obtain ⟨m, hm, rfl⟩ := hEle he
      exact ⟨m, (hmemFx m).2 ((MSP.mem_fixer.1 hm) w hwl), rfl⟩
    · intro e he
      rw [S5B.qv_baseA_eq h] at he
      obtain ⟨m, hm, rfl⟩ := he
      refine ⟨m, (hmemFx m).2 ?_, rfl⟩
      have h2 : a m = 1 := by
        obtain ⟨_, h2⟩ := (S5.mem_kerG a).1 (hd.pCoreOf_le_kerG h (Subgroup.mem_subgroupOf.1 hm))
        exact h2
      rw [h2, MSP.mat_one, Matrix.one_mulVec]
  have hw0 : w = 0 := by
    refine S5.eq_zero_of_fixed_aL hd h nv fun l' hl' => ?_
    obtain ⟨m, hm, hme⟩ := hle (S512N.ofA_mem_stab_baseA h.le ⟨l', h.L_le hl'⟩)
    rw [(puAmalgam h.le).ofA_injective hme] at hm
    exact (hmemFx _).1 hm
  have hu₀C : (u₀ : G) ∈ Subgroup.centralizer (L : Set G) := (nv.vec_eq_zero_iff _).1 hw0
  have hu₀D : (puAmalgam h.le).ofA u₀ ∈ S5.dSub h.le L (baseA _) := by
    rw [S5.dSub_baseA h, S512N.ofA_mem_imM_iff]
    exact ⟨Xq_le_pCoreOf M (h.Uq_le_Xq hu₀U), hu₀C⟩
  exact mul_mem hu₀D hdD

theorem commutator_zm_le_dSub_of_gen (h32 : S32) (h52 : S52) (h : PUHyp M T L)
    (hmin : PUMin M T L) (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {γ : Vtx (puAmalgam h.le)} (hβγ : (puAmalgam h.le).treeGraph.Adj (baseB _) γ)
    {l : Submodule F (MSP.V4 F)} (hl : S5.Case56 h (2 ^ k) a γ l)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hgen : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a (MSP.qLine l) →
      IsPGroup 2 E → (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E →
      S5.rconj y E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _)) :
    ⁅ZM _ (y⁻¹ • γ), ZM _ γ⁆ ≤ S5.dSub h.le L (baseA _) ⊓ XM _ (baseA (puAmalgam h.le)) := by
  have h51 := s51_of h32
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hαβ := adj_baseA_baseB (puAmalgam h.le)
  have hdist : ∀ ρ, (puAmalgam h.le).treeGraph.Adj (baseB _) ρ →
      (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2 := fun ρ hρ => by
    have := dist_triangle _ (baseA (puAmalgam h.le)) (baseB _) ρ
    rwa [dist_eq_one_of_adj _ hαβ, dist_eq_one_of_adj _ hρ] at this
  have hγM : IsMVtx _ γ := (isMVtx_iff_of_adj _ hβγ.symm).2 (not_isMVtx_baseB _)
  have hdγ := hdist γ hβγ
  have hdμ : (puAmalgam h.le).treeGraph.dist (baseA _) (y⁻¹ • γ) ≤ 2 := by
    have := dist_smul _ y⁻¹ (baseA (puAmalgam h.le)) γ
    rw [(mem_stab _).1 (inv_mem hy)] at this
    rw [this]
    exact hdγ
  have hμM : IsMVtx _ (y⁻¹ • γ) := (isMVtx_smul _ _ _).2 hγM
  have hZμ : ZM _ (y⁻¹ • γ) ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hμM (by rw [tdist_comm]; omega)
  have hZγ : ZM _ γ ≤ Qv _ (baseA (puAmalgam h.le)) :=
    zm_le_qv_of_dist_lt _ hγM (by rw [tdist_comm]; omega)
  have hB := S5C56.commutator_zm_qv_le_centralizer_jOff h hd hl.2.1 hl.2.2.2 hβγ hl.1
  have h1 : ⁅ZM _ (y⁻¹ • γ), ZM _ γ⁆ ≤ Subgroup.centralizer
      (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) : Set _) := by
    refine (Subgroup.commutator_mono hZμ le_rfl).trans ?_
    rw [Subgroup.commutator_comm]
    exact hB
  have h2 : ⁅ZM _ (y⁻¹ • γ), ZM _ γ⁆ ≤ Subgroup.centralizer
      (S5.rconj y (S5.jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _)) : Set _) := by
    refine (Subgroup.commutator_mono le_rfl hZγ).trans ?_
    have e1 : ZM _ (y⁻¹ • γ) = (ZM _ γ).map (MulAut.conj y⁻¹).toMonoidHom := zm_smul _ _ _
    have e2 : Qv _ (baseA (puAmalgam h.le)) =
        (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj y⁻¹).toMonoidHom := by
      rw [← qv_smul, (mem_stab _).1 (inv_mem hy)]
    rw [e1, e2, ← Subgroup.map_commutator, S5B.rconj_eq_map, PU.centralizer_map_mulEquiv]
    exact Subgroup.map_mono hB
  obtain ⟨α', hc, -⟩ := exists_isCritical_geo _ hyp hb0 hα hαβ
  have hRX : ⁅ZM _ (y⁻¹ • γ), ZM _ γ⁆ ≤ XM _ (baseA (puAmalgam h.le)) :=
    (Subgroup.commutator_mono (S5B.zm_le_vv_of_dist hμM hdμ)
      (S5B.zm_le_vv_of_dist hγM hdγ)).trans (h52 G M T L h hmin hb k F _ _ a hd α' hc).2.2.1
  have hRUD := (le_inf hRX h1).trans (s53_of h51 h32 G M T L h hmin hb k F _ _ a hd)
  intro r hr
  refine ⟨mem_dSub_of_comm_jOff h51 hd h hmin hb hl.2.1 hl.2.2.2 hy hgen (hRUD hr) ?_ ?_,
    hRX hr⟩
  · intro t ht
    rw [Subgroup.mem_centralizer_iff.1 (h1 hr) t ht]
    group
  · intro t ht
    rw [Subgroup.mem_centralizer_iff.1 (h2 hr) t ht]
    group

omit [Fintype F] in
theorem gen_g (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)} {l : Submodule F (MSP.V4 F)}
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hc56 : S5.Concl56 h (2 ^ k) a α' l g x) :
    ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a (MSP.qLine l) →
      IsPGroup 2 E → (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E →
      S5.rconj g E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _) := by
  intro E hE hE2 hErel
  refine hc56.1 (S5.rconj g E) E (hE2.map _) hE2 ((S5B.rconj_le_rconj_iff (g := g)).2 hE) hE ?_
    hErel
  rw [S5C56.relIndex_rconj h hg]
  exact hErel

omit [Fintype F] in
theorem gen_gx (h : PUHyp M T L) {l : Submodule F (MSP.V4 F)}
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ stab _ (baseA (puAmalgam h.le))) (hopp : S5.Opp56 h (2 ^ k) a l g x) :
    ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a (MSP.qLine l) →
      IsPGroup 2 E → (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E →
      S5.rconj (g * x) E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _) := by
  intro E hE hE2 hErel
  refine hopp (S5.rconj (g * x) E) E (hE2.map _) hE2
    ((S5B.rconj_le_rconj_iff (g := g * x)).2 hE) hE ?_ hErel
  rw [S5C56.relIndex_rconj h (mul_mem hg hx)]
  exact hErel

omit [Fintype F] in
theorem opp56_of_mem_stab (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} {g x : (puAmalgam h.le).Universal}
    (hx : x ∈ stab _ (baseA (puAmalgam h.le))) (hc56 : S5.Concl56 h (2 ^ k) a α' l g x)
    (hxP : x ∈ S5.vPre h.le a (MSP.stab l)) : S5.Opp56 h (2 ^ k) a l g x := by
  intro E₁ E₂ hE₁ hE₂ hle₁ hle₂ hr₁ hr₂
  have hN : S5.vPre h.le a (MSP.stab l) ≤ Subgroup.normalizer
      (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) :=
    S5C56.vPre_le_normalizer_vPre h.le (MSP.stab_le_normalizer_fixer l)
  have hrx : S5.rconj x⁻¹ (S5.vPre h.le a (MSP.qLine l)) = S5.vPre h.le a (MSP.qLine l) := by
    rw [S5B.rconj_eq_map, inv_inv]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hN hxP)
  have hinv : ∀ K : Subgroup (puAmalgam h.le).Universal, S5.rconj x⁻¹ (S5.rconj x K) = K := by
    intro K
    have := S5B.rconj_rconj_inv x⁻¹ K
    rwa [inv_inv] at this
  have h1 : S5.rconj x⁻¹ E₁ ≤ S5.rconj g (S5.vPre h.le a (MSP.qLine l)) := by
    have := (S5B.rconj_le_rconj_iff (g := x⁻¹)).2 hle₁
    rwa [S5B.rconj_mul, hinv] at this
  have h2 : S5.rconj x⁻¹ E₂ ≤ S5.vPre h.le a (MSP.qLine l) := by
    rw [← hrx]
    exact (S5B.rconj_le_rconj_iff (g := x⁻¹)).2 hle₂
  have h0 := hc56.1 (S5.rconj x⁻¹ E₁) (S5.rconj x⁻¹ E₂) (hE₁.map _) (hE₂.map _) h1 h2
    (by rw [S5C56.relIndex_rconj h (inv_mem hx)]; exact hr₁)
    (by rw [S5C56.relIndex_rconj h (inv_mem hx)]; exact hr₂)
  have h3 := congrArg (S5.rconj x) h0
  have hQx : S5.rconj x (Qv _ (baseA (puAmalgam h.le))) = Qv _ (baseA (puAmalgam h.le)) := by
    rw [S5B.rconj_eq_map, ← qv_smul, (mem_stab _).1 (inv_mem hx)]
  rwa [S5B.rconj_sup, S5B.rconj_sup, S5B.rconj_rconj_inv, S5B.rconj_rconj_inv, hQx,
    S5B.rconj_eq_self_of_mem hx] at h3

@[expose] def Cent56F : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ l : Submodule F (MSP.V4 F),
        S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
      ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
        S5.Concl56 h (2 ^ k) a α' l g x → S5.Opp56 h (2 ^ k) a l g x →
        ∀ μ : Vtx (puAmalgam h.le),
          (μ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
            μ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) →
          ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
            stabCenter _ (baseA (puAmalgam h.le))

end S512R

end CFSG.Quasithin.MS93

module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Basic
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private theorem mem_centralizer_V_of_commutator_mem (hS : Sec6Hyp M V) {x : G}
    (hxP : ∀ p ∈ Pc M V, ⁅x, p⁆ ∈ V) : x ∈ Subgroup.centralizer (V : Set G) := by
  classical
  have h : Hyp M V := hS.sec5.toRootHyp.toHyp
  have hVcent : V ≤ Subgroup.centralizer (Pc M V : Set G) :=
    h.center_Pc.symm.trans_le inf_le_right
  have hVab : IsMulCommutative ↥V := h.maxAb.prop.2.2
  have hPP : ⁅Pc M V, Pc M V⁆ = V := hS.sec5.commutator_Pc_eq_V hS.ne
  have hfix : ∀ p ∈ Pc M V, ∀ q ∈ Pc M V, x * ⁅p, q⁆ * x⁻¹ = ⁅p, q⁆ := by
    intro p hp q hq
    have hxp : ⁅x, p⁆ ∈ V := hxP p hp
    have hxq : ⁅x, q⁆ ∈ V := hxP q hq
    have hcomm : ∀ a ∈ V, ∀ b ∈ Pc M V, a * b = b * a := by
      intro a ha b hb
      exact ((Subgroup.mem_centralizer_iff.mp (hVcent ha)) b hb).symm
    have htriv : ⁅⁅x, p⁆, ⁅x, q⁆⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val (hVab.is_comm.comm ⟨⁅x, p⁆, hxp⟩ ⟨⁅x, q⁆, hxq⟩)
    have hxp' : x * p * x⁻¹ = ⁅x, p⁆ * p := by rw [commutatorElement_def]; group
    have hxq' : x * q * x⁻¹ = ⁅x, q⁆ * q := by rw [commutatorElement_def]; group
    rw [conjugate_commutatorElement, hxp', hxq',
      CFSG.GroupTheory.commutatorElement_mul_of_commute hcomm hxp hxq hp hq, htriv, one_mul]
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← hPP, Subgroup.commutator_def] at hv
  have hle : Subgroup.closure {g : G | ∃ p ∈ Pc M V, ∃ q ∈ Pc M V, ⁅p, q⁆ = g} ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine (Subgroup.closure_le (K := Subgroup.centralizer ({x} : Set G))).mpr ?_
    rintro v ⟨p, hp, q, hq, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hconj := hfix p hp q hq
    show x * ⁅p, q⁆ = ⁅p, q⁆ * x
    calc x * ⁅p, q⁆ = (x * ⁅p, q⁆ * x⁻¹) * x := by group
      _ = ⁅p, q⁆ * x := by rw [hconj]
  exact (Subgroup.mem_centralizer_iff.mp (hle hv) x (Set.mem_singleton x)).symm

theorem Sec6Hyp.mem_Pc_of_commutator_mem (hS : Sec6Hyp M V) {x : G} (hx : x ∈ M)
    (hxP : ∀ p ∈ Pc M V, ⁅x, p⁆ ∈ V) : x ∈ Pc M V := by
  have h : Hyp M V := hS.sec5.toRootHyp.toHyp
  have hxV : x ∈ Subgroup.centralizer (V : Set G) := mem_centralizer_V_of_commutator_mem hS hxP
  obtain ⟨U, hU⟩ := hS.ne
  obtain ⟨g, y, hshape, -⟩ := hS.sec5.exists_sigma_data hU
  refine Sec45Shape.mem_Pc_of_commutator_mem hS.sec5.toRootHyp hshape hx hxV ?_
  intro p hp
  rw [← commutatorElement_inv]
  exact V.inv_mem (hxP p hp)

private theorem exists_twoElement_lift (hS : Sec6Hyp M V)
    {z : ↥(Subgroup.centralizer (imgQ M (m0Of M V) : Set (MBar M)))} (hzord : orderOf z = 2) :
    ∃ t : G, t ∈ M ∧ t ∉ Pc M V ∧ t ^ 2 ∈ Pc M V ∧
      ∀ m ∈ m0Of M V, ⁅t, m⁆ ∈ Pc M V := by
  classical
  set zM : MBar M := (z : MBar M) with hzM
  have hzM_ne : zM ≠ 1 := by
    intro h1
    have h2 : z = 1 := Subtype.ext h1
    rw [h2] at hzord
    exact absurd hzord (by norm_num)
  have hzM_sq : zM ^ 2 = 1 := by
    have h1 : z ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hzord]
    have h2 := congrArg (fun w : ↥(Subgroup.centralizer
      (imgQ M (m0Of M V) : Set (MBar M))) => (w : MBar M)) h1
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
    simpa [zM] using h2
  have hzM_cent : ∀ y ∈ imgQ M (m0Of M V), y * zM = zM * y :=
    fun y hy => Subgroup.mem_centralizer_iff.mp z.2 y hy
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (pCore 2 ↥M) zM
  set t : G := (x : G) with ht
  have htM : t ∈ M := x.2
  have ht_notP : t ∉ Pc M V := by
    intro htP
    have h1 : QuotientGroup.mk' (pCore 2 ↥M) x = 1 := (hS.mk_eq_one_iff x).mpr htP
    rw [hx] at h1
    exact hzM_ne h1
  have ht2P : t ^ 2 ∈ Pc M V := by
    have h1 : QuotientGroup.mk' (pCore 2 ↥M) (x ^ 2) = 1 := by
      rw [map_pow, hx]
      exact hzM_sq
    simpa [t] using (hS.mk_eq_one_iff (x ^ 2)).mp h1
  have htcent : ∀ m ∈ m0Of M V, ⁅t, m⁆ ∈ Pc M V := by
    intro m hm
    have hmM : m ∈ M := hS.sec5.m0Of_le_M hm
    have hy : QuotientGroup.mk' (pCore 2 ↥M) ⟨m, hmM⟩ ∈ imgQ M (m0Of M V) :=
      mk_mem_imgQ hm
    have h1 : ⁅zM, QuotientGroup.mk' (pCore 2 ↥M) ⟨m, hmM⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (hzM_cent _ hy).symm
    have h2 : QuotientGroup.mk' (pCore 2 ↥M) ⁅x, ⟨m, hmM⟩⁆ = 1 := by
      rw [map_commutatorElement, hx]
      exact h1
    have h3 : ((⁅x, ⟨m, hmM⟩⁆ : ↥M) : G) ∈ Pc M V := (hS.mk_eq_one_iff _).mp h2
    have h4 : ((⁅x, ⟨m, hmM⟩⁆ : ↥M) : G) = ⁅t, m⁆ := by
      change (Subgroup.subtype M) ⁅x, ⟨m, hmM⟩⁆ = ⁅t, m⁆
      rw [map_commutatorElement]
      simp [t]
    rwa [h4] at h3
  exact ⟨t, htM, ht_notP, ht2P, htcent⟩

private theorem m0Of_conj_mem_commMemSubgroup (hS : Sec6Hyp M V) {t : G} (htM : t ∈ M)
    (htcent : ∀ m ∈ m0Of M V, ⁅t, m⁆ ∈ Pc M V)
    (hPV : Pc M V ≤ Subgroup.normalizer (V : Set G)) :
    ∀ m ∈ m0Of M V, ∀ y ∈ CFSG.GroupTheory.commMemSubgroup (Pc M V) V hPV t,
      m * y * m⁻¹ ∈ CFSG.GroupTheory.commMemSubgroup (Pc M V) V hPV t := by
  classical
  have h : Hyp M V := hS.sec5.toRootHyp.toHyp
  intro m hm y hy
  have hyP : y ∈ Pc M V := ((CFSG.GroupTheory.mem_commMemSubgroup hPV t y).mp hy).1
  have hytV : ⁅y, t⁆ ∈ V := ((CFSG.GroupTheory.mem_commMemSubgroup hPV t y).mp hy).2
  have hmM : m ∈ M := hS.sec5.m0Of_le_M hm
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := h.le_normalizer hmM
  have hmP : m ∈ Subgroup.normalizer (Pc M V : Set G) := h.le_normalizer_Pc hmM
  have hmtP : ⁅m, t⁆ ∈ Pc M V := by
    simpa [commutatorElement_inv] using (Pc M V).inv_mem (htcent m hm)
  have hu : m * t * m⁻¹ = ⁅m, t⁆ * t := by rw [commutatorElement_def]; group
  set p : G := ⁅m, t⁆ with hp
  set y' : G := m * y * m⁻¹ with hy'
  have hy'P : y' ∈ Pc M V := (Subgroup.mem_normalizer_iff.mp hmP y).mp hyP
  have hyuV : ⁅y', p * t⁆ ∈ V := by
    rw [← hu, ← conjugate_commutatorElement]
    exact (Subgroup.mem_normalizer_iff.mp hmV ⁅y, t⁆).mp hytV
  have hpP : p ∈ Pc M V := hmtP
  have hsplit : ⁅y', p * t⁆ = ⁅y', p⁆ * p * ⁅y', t⁆ * p⁻¹ :=
    commutatorElement_mul_right_eq_mul_conj y' p t
  have hypV : ⁅y', p⁆ ∈ V := by
    rw [← hS.sec5.commutator_Pc_eq_V hS.ne]
    exact Subgroup.commutator_mem_commutator hy'P hpP
  have hw : p * ⁅y', t⁆ * p⁻¹ ∈ V := by
    have h1 : ⁅y', p⁆ * (p * ⁅y', t⁆ * p⁻¹) ∈ V := by
      have h := hyuV
      rw [hsplit] at h
      simpa [mul_assoc] using h
    have h2 : p * ⁅y', t⁆ * p⁻¹ =
        ⁅y', p⁆⁻¹ * (⁅y', p⁆ * (p * ⁅y', t⁆ * p⁻¹)) := by group
    rw [h2]
    exact V.mul_mem (V.inv_mem hypV) h1
  have hyt' : ⁅y', t⁆ ∈ V := by
    have hpcent : p * (p * ⁅y', t⁆ * p⁻¹) = (p * ⁅y', t⁆ * p⁻¹) * p := by
      have hVcent : V ≤ Subgroup.centralizer (Pc M V : Set G) :=
        h.center_Pc.symm.trans_le inf_le_right
      exact Subgroup.mem_centralizer_iff.mp (hVcent hw) p hpP
    have hone : p * ⁅y', t⁆ * p⁻¹ = ⁅y', t⁆ := by
      calc p * ⁅y', t⁆ * p⁻¹ = p⁻¹ * (p * (p * ⁅y', t⁆ * p⁻¹)) := by group
        _ = p⁻¹ * ((p * ⁅y', t⁆ * p⁻¹) * p) := by rw [hpcent]
        _ = ⁅y', t⁆ := by group
    rw [← hone]
    exact hw
  rw [CFSG.GroupTheory.mem_commMemSubgroup]
  exact ⟨hy'P, hyt'⟩

private theorem m0Of_le_normalizer_commMemSubgroup (hS : Sec6Hyp M V) {t : G} (htM : t ∈ M)
    (htcent : ∀ m ∈ m0Of M V, ⁅t, m⁆ ∈ Pc M V)
    (hPV : Pc M V ≤ Subgroup.normalizer (V : Set G)) :
    m0Of M V ≤ Subgroup.normalizer
      (CFSG.GroupTheory.commMemSubgroup (Pc M V) V hPV t : Set G) := by
  intro m hm
  refine Subgroup.mem_normalizer_iff.mpr fun y =>
    ⟨m0Of_conj_mem_commMemSubgroup hS htM htcent hPV m hm y, fun hy => ?_⟩
  have h1 := m0Of_conj_mem_commMemSubgroup hS htM htcent hPV m⁻¹ ((m0Of M V).inv_mem hm)
    (m * y * m⁻¹) hy
  simpa [mul_assoc] using h1

private theorem isPGroup_sup_zpowers_Pc (hS : Sec6Hyp M V) {t : G} (htM : t ∈ M)
    (ht2P : t ^ 2 ∈ Pc M V) : IsPGroup 2 ↥(Subgroup.zpowers t ⊔ Pc M V) := by
  have h : Hyp M V := hS.sec5.toRootHyp.toHyp
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hzp2 : IsPGroup 2 (Subgroup.zpowers t) := by
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hP2 ⟨t ^ 2, ht2P⟩
    have htk : t ^ 2 ^ (k + 1) = 1 := by
      have h1 : (t ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [pow_succ', pow_mul]
      exact h1
    have hdvd : Nat.card ↥(Subgroup.zpowers t) ∣ 2 ^ (k + 1) := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one htk
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨n, -, hcard⟩
    exact IsPGroup.of_card hcard
  have hzp_norm : Subgroup.zpowers t ≤ Subgroup.normalizer (Pc M V : Set G) :=
    Subgroup.zpowers_le.mpr (h.le_normalizer_Pc htM)
  exact hzp2.to_sup_of_normal_right' hP2 hzp_norm

private theorem Sec6Hyp.Pc_ne_V (hS : Sec6Hyp M V) : Pc M V ≠ V := by
  intro heq
  have hbot : ⁅Pc M V, Pc M V⁆ = ⊥ := by
    rw [heq]
    exact Subgroup.commutator_self_eq_bot_iff.mpr hS.sec5.toRootHyp.toHyp.maxAb.prop.2.2
  rw [hS.sec5.commutator_Pc_eq_V hS.ne] at hbot
  exact hS.sec5.toRootHyp.toHyp.ne_bot hbot

private theorem exists_central_coset (hS : Sec6Hyp M V) {t : G} (htM : t ∈ M)
    (ht2P : t ^ 2 ∈ Pc M V) :
    ∃ x ∈ Pc M V, x ∉ V ∧ ∀ g ∈ Subgroup.zpowers t ⊔ Pc M V, ⁅x, g⁆ ∈ V := by
  classical
  have h : Hyp M V := hS.sec5.toRootHyp.toHyp
  have hPV : Pc M V ≤ Subgroup.normalizer (V : Set G) := h.Pc_le_M.trans h.le_normalizer
  set T : Subgroup G := Subgroup.zpowers t ⊔ Pc M V with hT
  have hT2 : IsPGroup 2 T := isPGroup_sup_zpowers_Pc hS htM ht2P
  have hT_le_M : T ≤ M := by
    rw [hT]
    exact sup_le (Subgroup.zpowers_le.mpr htM) h.Pc_le_M
  have hV_le_T : V ≤ T := by
    rw [hT]
    exact h.le_Pc.trans le_sup_right
  have hVnormal : (V.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hV_le_T).mpr (hT_le_M.trans h.le_normalizer)
  have hPT_normal : ((Pc M V).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : Pc M V ≤ T)).mpr
      (hT_le_M.trans h.le_normalizer_Pc)
  letI : (V.subgroupOf T).Normal := hVnormal
  let E : Type := ↥T ⧸ V.subgroupOf T
  haveI : Finite E := inferInstance
  have hE2 : IsPGroup 2 E := hT2.to_quotient (V.subgroupOf T)
  let Nq : Subgroup E := ((Pc M V).subgroupOf T).map (QuotientGroup.mk' (V.subgroupOf T))
  haveI : Nq.Normal := hPT_normal.map (QuotientGroup.mk' (V.subgroupOf T))
    (QuotientGroup.mk'_surjective _)
  have hNq_ne : Nq ≠ ⊥ := by
    intro hbot
    apply hS.Pc_ne_V
    refine le_antisymm ?_ h.le_Pc
    intro y hy
    have hyT : y ∈ T := by rw [hT]; exact Subgroup.mem_sup_right hy
    have hmem : QuotientGroup.mk' (V.subgroupOf T) ⟨y, hyT⟩ ∈ Nq :=
      Subgroup.mem_map.mpr ⟨⟨y, hyT⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    rw [hbot] at hmem
    have h1 : QuotientGroup.mk' (V.subgroupOf T) ⟨y, hyT⟩ = 1 := by simpa using hmem
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  obtain ⟨w, hw_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hE2 Nq hNq_ne)
  set wE : E := (w : E) with hwE
  obtain ⟨y, hyPsub, hyw⟩ := Subgroup.mem_map.mp w.2.1
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hyPsub, ?_, ?_⟩
  · intro hV
    have hyV : y ∈ V.subgroupOf T := Subgroup.mem_subgroupOf.mpr hV
    have h1 : QuotientGroup.mk' (V.subgroupOf T) y = 1 := (QuotientGroup.eq_one_iff y).mpr hyV
    rw [hyw] at h1
    exact (fun hw1 => hw_ne (Subtype.ext hw1)) h1
  · intro g hgT
    have hcenter : wE * QuotientGroup.mk' (V.subgroupOf T) ⟨g, hgT⟩ =
        QuotientGroup.mk' (V.subgroupOf T) ⟨g, hgT⟩ * wE :=
      (Subgroup.mem_center_iff.mp w.2.2 _).symm
    have h1 : QuotientGroup.mk' (V.subgroupOf T) ⁅y, ⟨g, hgT⟩⁆ = 1 := by
      rw [map_commutatorElement, hyw]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hcenter
    have h2 : ⁅y, ⟨g, hgT⟩⁆ ∈ V.subgroupOf T := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : ((⁅y, ⟨g, hgT⟩⁆ : T) : G) ∈ V := Subgroup.mem_subgroupOf.mp h2
    have h4 : ((⁅y, ⟨g, hgT⟩⁆ : T) : G) = ⁅(y : G), g⁆ := by
      change (Subgroup.subtype T) ⁅y, ⟨g, hgT⟩⁆ = ⁅(y : G), g⁆
      rw [map_commutatorElement]
      rfl
    rwa [h4] at h3

private theorem exists_mem_Pc_not_mem_V_of_sq_mem (hS : Sec6Hyp M V) {t : G} (htM : t ∈ M)
    (ht2P : t ^ 2 ∈ Pc M V) : ∃ x ∈ Pc M V, x ∉ V ∧ ⁅x, t⁆ ∈ V := by
  obtain ⟨x, hxP, hxV, hxT⟩ := exists_central_coset hS htM ht2P
  exact ⟨x, hxP, hxV, hxT t (Subgroup.mem_sup_left (Subgroup.mem_zpowers t))⟩

theorem Sec6Hyp.odd_card_centralizer_imgQ_m0Of (hS : Sec6Hyp M V) (h71 : Sec7.Stmt71 M V) :
    Odd (Nat.card ↥(Subgroup.centralizer (imgQ M (m0Of M V) : Set (MBar M)))) := by
  classical
  have h : Hyp M V := hS.sec5.toRootHyp.toHyp
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer (imgQ M (m0Of M V) : Set (MBar M))))
      2 hodd.two_dvd
  obtain ⟨t, htM, ht_notP, ht2P, htcent⟩ := exists_twoElement_lift hS hzord
  have hPV : Pc M V ≤ Subgroup.normalizer (V : Set G) := h.Pc_le_M.trans h.le_normalizer
  set N : Subgroup G := CFSG.GroupTheory.commMemSubgroup (Pc M V) V hPV t with hN
  have hN_le_P : N ≤ Pc M V := CFSG.GroupTheory.commMemSubgroup_le (Pc M V) V hPV t
  have hV_le_N : V ≤ N := by
    intro v hv
    rw [hN, CFSG.GroupTheory.mem_commMemSubgroup]
    refine ⟨h.le_Pc hv, ?_⟩
    have hconj : t * v⁻¹ * t⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (h.le_normalizer htM) v⁻¹).mp (V.inv_mem hv)
    have hmem : v * (t * v⁻¹ * t⁻¹) ∈ V := V.mul_mem hv hconj
    simpa [commutatorElement_def, mul_assoc] using hmem
  have hN_norm : m0Of M V ≤ Subgroup.normalizer (N : Set G) :=
    m0Of_le_normalizer_commMemSubgroup hS htM htcent hPV
  have hN_ne_V : N ≠ V := by
    obtain ⟨x0, hx0P, hx0V, hx0tV⟩ := exists_mem_Pc_not_mem_V_of_sq_mem hS htM ht2P
    intro hNV
    have hx0N : x0 ∈ N := by
      rw [hN, CFSG.GroupTheory.mem_commMemSubgroup]
      exact ⟨hx0P, hx0tV⟩
    rw [hNV] at hx0N
    exact hx0V hx0N
  have hN_eq : N = Pc M V := (h71 N hV_le_N hN_le_P hN_norm).resolve_left hN_ne_V
  have htP : t ∈ Pc M V := by
    refine hS.mem_Pc_of_commutator_mem htM ?_
    intro y hy
    have hyN : y ∈ N := by rw [hN_eq]; exact hy
    have hytV : ⁅y, t⁆ ∈ V :=
      ((CFSG.GroupTheory.mem_commMemSubgroup hPV t y).mp (hN ▸ hyN)).2
    simpa [commutatorElement_inv] using V.inv_mem hytV
  exact ht_notP htP

end CFSG.RankThree.GF2n.Tim81

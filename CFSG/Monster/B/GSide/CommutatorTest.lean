module

public import CFSG.Monster.B.GSide.FusionBasic
public import CFSG.Monster.B.GSide.HSylowCenter

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam
  CFSG.Monster.B.TwoA.Sp8

theorem cV0_mem_center_vStab :
    cV0 ∈ Subgroup.center (vStab cv0) := by
  rw [center_vStab_cv0]
  exact Subgroup.mem_zpowers _

theorem cV0_mul_mem_centralizer
    (y : vStab cv0) : cV0 * y ∈ Subgroup.centralizer {y} :=
  Subgroup.mul_mem _ (cV0_mem_centralizer y) (mem_centralizer_singleton_self y)

theorem centralizer_cV0_mul
    (y : vStab cv0) :
    Subgroup.centralizer {cV0 * y} = Subgroup.centralizer {y} := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hc : x * cV0 = cV0 * x := Subgroup.mem_center_iff.1 cV0_mem_center_vStab x
  constructor
  · intro h
    refine mul_left_cancel (a := cV0) ?_
    calc cV0 * (x * y) = x * (cV0 * y) := by simp only [← mul_assoc, hc]
      _ = cV0 * y * x := h
      _ = cV0 * (y * x) := mul_assoc _ _ _
  · intro h
    calc x * (cV0 * y) = cV0 * (x * y) := by simp only [← mul_assoc, hc]
      _ = cV0 * (y * x) := by rw [h]
      _ = cV0 * y * x := (mul_assoc _ _ _).symm

theorem ne_one_of_mem_RA
    {y : vStab cv0} (hy : y ∈ RA) : y ≠ 1 := by
  obtain ⟨w, -, hw⟩ := hy
  intro h
  apply clabelS_ne_one w
  rw [← hw, h]
  rfl

theorem ne_cV0_of_mem_RA
    {y : vStab cv0} (hy : y ∈ RA) : y ≠ cV0 := by
  obtain ⟨w, hw, hyw⟩ := hy
  intro h
  apply (clabel_adj hw).1
  have e : clabelS w = clabelS cv0 := by rw [← hyw, h, coe_cV0]
  exact (congrArg Subtype.val e).symm

theorem ne_one_of_mem_RB
    {y : vStab cv0} (hy : y ∈ RB) : y ≠ 1 := by
  intro h
  have hr : cV0 * y ∈ RA := hy
  rw [h, mul_one] at hr
  exact ne_cV0_of_mem_RA hr rfl

theorem ne_cV0_of_mem_RB
    {y : vStab cv0} (hy : y ∈ RB) : y ≠ cV0 := by
  intro h
  have hr : cV0 * y ∈ RA := hy
  rw [h, cV0_mul_self] at hr
  exact ne_one_of_mem_RA hr rfl

section Generic

variable {K K' D : Type*} [Group K] [Group K'] [Group D]

theorem commutator_pCore_eq_of_map {F : K →* D} (hF : Function.Injective F) {N : Subgroup D}
    (hN : (CFSG.pCore 2 K).map F = N) {x : D} (hx : ⁅N, N⁆ = Subgroup.zpowers x) {k : K}
    (hk : F k = x) : ⁅CFSG.pCore 2 K, CFSG.pCore 2 K⁆ = Subgroup.zpowers k := by
  apply Subgroup.map_injective hF
  rw [Subgroup.map_commutator, hN, MonoidHom.map_zpowers, hk, hx]

theorem commutator_pCore_eq_of_equiv (e : K ≃* K') {k : K}
    (h : ⁅CFSG.pCore 2 K, CFSG.pCore 2 K⁆ = Subgroup.zpowers k) :
    ⁅CFSG.pCore 2 K', CFSG.pCore 2 K'⁆ = Subgroup.zpowers (e k) := by
  rw [← CFSG.pCore_map_iso 2 e, ← Subgroup.map_commutator, h, MonoidHom.map_zpowers]
  rfl

private theorem zpowers_ne_zpowers_of_orderOf_eq_two {k c : K} (hc : orderOf c = 2) (hk1 : k ≠ 1)
    (hkc : k ≠ c) : Subgroup.zpowers k ≠ Subgroup.zpowers c := fun h => by
  have hk : k ∈ Subgroup.zpowers c := h ▸ Subgroup.mem_zpowers k
  rcases (mem_zpowers_iff_of_orderOf_eq_two hc).1 hk with h1 | h1
  · exact hk1 h1
  · exact hkc h1

private theorem conj_mul_of_commute {c a b g : K} (hc : g * c = c * g) (h : g * a * g⁻¹ = b) :
    g * (c * a) * g⁻¹ = c * b := by
  rw [← h, ← mul_assoc, hc]
  group

private theorem mul_mul_cancel_of_mul_self {c y : K} (hc : c * c = 1) : c * (c * y) = y := by
  rw [← mul_assoc, hc, one_mul]

private theorem mul_self_of_orderOf_eq_two {r : K} (hr : orderOf r = 2) : r * r = 1 := by
  rw [← sq, ← hr, pow_orderOf_eq_one]

private theorem mul_self_of_mul_mul_self {c y : K} (hc : c * c = 1) (hcy : c * y = y * c)
    (h : c * y * (c * y) = 1) : y * y = 1 := by
  calc y * y = c * c * (y * y) := by rw [hc, one_mul]
    _ = c * y * (c * y) := by
        rw [mul_assoc c y (c * y), ← mul_assoc y c y, ← hcy]
        group
    _ = 1 := h

private theorem mul_ne_one_of_ne {c y : K} (hc : c * c = 1) (hyc : y ≠ c) : c * y ≠ 1 := fun h =>
  hyc ((eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right hc))

private theorem mul_ne_self_of_ne_one {c y : K} (hy : y ≠ 1) : c * y ≠ c := fun h =>
  hy (mul_left_cancel (h.trans (mul_one c).symm))

end Generic

theorem orderOf_of_mem_RA
    {y : vStab cv0} (hy : y ∈ RA) : orderOf y = 2 := by
  obtain ⟨w, -, hw⟩ := hy
  exact (Subgroup.orderOf_coe y).symm.trans ((congrArg orderOf hw).trans (orderOf_clabelS w))

theorem commute_cV0
    (y : vStab cv0) : cV0 * y = y * cV0 :=
  (Subgroup.mem_center_iff.1 cV0_mem_center_vStab y).symm

theorem orderOf_of_mem_RA_or_RB
    {y : vStab cv0} (hy : y ∈ RA ∪ RB) : orderOf y = 2 := by
  rcases hy with hy | hy
  · exact orderOf_of_mem_RA hy
  · have hr : cV0 * y ∈ RA := hy
    exact orderOf_eq_prime (by
      rw [sq]
      exact mul_self_of_mul_mul_self cV0_mul_self (commute_cV0 y)
        (mul_self_of_orderOf_eq_two (orderOf_of_mem_RA hr))) (ne_one_of_mem_RB hy)

abbrev pCoreComm
    (y : vStab cv0) : Subgroup (Subgroup.centralizer {y}) :=
  ⁅CFSG.pCore 2 (Subgroup.centralizer {y}), CFSG.pCore 2 (Subgroup.centralizer {y})⁆

theorem pCoreComm_map_equiv
    {y y' : vStab cv0}
    (e : Subgroup.centralizer {y} ≃* Subgroup.centralizer {y'}) :
    (pCoreComm y).map e.toMonoidHom = pCoreComm y' := by
  rw [Subgroup.map_commutator, CFSG.pCore_map_iso]

theorem mem_centralizer_lamW0H_iff
    {x : vStab cv0} :
    x ∈ Subgroup.centralizer {lamW0H} ↔ ((x : Shat) : Dfull) ∈ Pc 0 := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← mem_cEdgeFix_iff]
  constructor
  · intro h
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [mem_vStab, ← commute_clabel_iff]
    exact congrArg (fun z : vStab cv0 => ((z : Shat) : Dfull)) h
  · intro h
    exact Subtype.ext (Subtype.ext ((commute_clabel_iff cw0 x).2 (Subgroup.mem_inf.1 h).2))

@[expose] def centralizerLamW0Equiv :
    Subgroup.centralizer {lamW0H} ≃* P1 where
  toFun x := ⟨((x : vStab cv0) : Shat), mem_centralizer_lamW0H_iff.1 x.2⟩
  invFun p := ⟨⟨⟨p, Eam_le_Shat (Pc_le_Eam 0 p.2)⟩, mem_vStab_cv0.2 (Pc_le_Eam 0 p.2)⟩,
    mem_centralizer_lamW0H_iff.2 p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem coe_centralizerLamW0Equiv
    (x : Subgroup.centralizer {lamW0H}) :
    ((centralizerLamW0Equiv x : P1) : Dfull) = (((x : vStab cv0) : Shat) : Dfull) := rfl

theorem commutator_N1_eq_zpowers :
    ⁅N1, N1⁆ = Subgroup.zpowers xhat := by
  have h := congrArg (Subgroup.map N1.subtype) commutator_N1
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 (Subgroup.zpowers_le.2 xhat_mem_N1)] at h
  exact h

theorem pCoreComm_lamW0H :
    pCoreComm lamW0H = Subgroup.zpowers ⟨cV0 * lamW0H, cV0_mul_mem_centralizer lamW0H⟩ := by
  have hFinj : Function.Injective (P1.subtype.comp centralizerLamW0Equiv.toMonoidHom) :=
    P1.subtype_injective.comp centralizerLamW0Equiv.injective
  have hO : (CFSG.pCore 2 (Subgroup.centralizer {lamW0H})).map
      (P1.subtype.comp centralizerLamW0Equiv.toMonoidHom) = N1 := by
    rw [← Subgroup.map_map, CFSG.pCore_map_iso, pCore_P1]
  have hval : (P1.subtype.comp centralizerLamW0Equiv.toMonoidHom)
      ⟨cV0 * lamW0H, cV0_mul_mem_centralizer lamW0H⟩ = xhat := by
    show clabel cv0 * clabel cw0 = xhat
    rw [clabel_cv0, clabel_cw0, ← mul_assoc, cQ_mul_self, one_mul]
  exact commutator_pCore_eq_of_map hFinj hO commutator_N1_eq_zpowers hval

theorem pCoreComm_of_mem_RA
    {y : vStab cv0} (hy : y ∈ RA) :
    pCoreComm y = Subgroup.zpowers ⟨cV0 * y, cV0_mul_mem_centralizer y⟩ := by
  obtain ⟨h, hh⟩ := isConj_iff.1 ((mem_RA_iff_isConj y).1 hy)
  have he : (centralizerConjEquiv h hh).symm ⟨cV0 * lamW0H, cV0_mul_mem_centralizer lamW0H⟩ =
      ⟨cV0 * y, cV0_mul_mem_centralizer y⟩ :=
    Subtype.ext (conj_mul_of_commute (Subgroup.mem_center_iff.1 cV0_mem_center_vStab h) hh)
  exact (commutator_pCore_eq_of_equiv (centralizerConjEquiv h hh).symm pCoreComm_lamW0H).trans
    (congrArg Subgroup.zpowers he)

theorem pCoreComm_of_mem_RB
    {y : vStab cv0} (hy : y ∈ RB) :
    pCoreComm y = Subgroup.zpowers ⟨y, mem_centralizer_singleton_self y⟩ := by
  have hr : cV0 * y ∈ RA := hy
  have he : MulEquiv.subgroupCongr (centralizer_cV0_mul y)
      ⟨cV0 * (cV0 * y), cV0_mul_mem_centralizer (cV0 * y)⟩ =
      ⟨y, mem_centralizer_singleton_self y⟩ :=
    Subtype.ext (mul_mul_cancel_of_mul_self cV0_mul_self)
  exact (commutator_pCore_eq_of_equiv (MulEquiv.subgroupCongr (centralizer_cV0_mul y))
    (pCoreComm_of_mem_RA hr)).trans (congrArg Subgroup.zpowers he)

theorem pCoreComm_ne_zpowers_cV0
    {y : vStab cv0} (hy : y ∈ RA ∪ RB) :
    pCoreComm y ≠ Subgroup.zpowers ⟨cV0, cV0_mem_centralizer y⟩ := by
  have hc2 : orderOf (⟨cV0, cV0_mem_centralizer y⟩ : Subgroup.centralizer {y}) = 2 :=
    (Subgroup.orderOf_mk cV0 _).trans orderOf_cV0
  rcases hy with hy | hy
  · intro h
    refine zpowers_ne_zpowers_of_orderOf_eq_two hc2 (fun h1 => ?_) (fun h1 => ?_)
      ((pCoreComm_of_mem_RA hy).symm.trans h)
    · exact mul_ne_one_of_ne cV0_mul_self (ne_cV0_of_mem_RA hy) (congrArg Subtype.val h1)
    · exact mul_ne_self_of_ne_one (ne_one_of_mem_RA hy) (congrArg Subtype.val h1)
  · intro h
    refine zpowers_ne_zpowers_of_orderOf_eq_two hc2 (fun h1 => ?_) (fun h1 => ?_)
      ((pCoreComm_of_mem_RB hy).symm.trans h)
    · exact ne_one_of_mem_RB hy (congrArg Subtype.val h1)
    · exact ne_cV0_of_mem_RB hy (congrArg Subtype.val h1)

theorem natCard_centralizer_of_mem_RA_or_RB
    {y : vStab cv0} (hy : y ∈ RA ∪ RB) :
    Nat.card (Subgroup.centralizer {y}) = 77148607752437760 := by
  have hRA : ∀ {r : vStab cv0}, r ∈ RA →
      Nat.card (Subgroup.centralizer {r}) = 77148607752437760 := fun {r} hr => by
    obtain ⟨h, hh⟩ := isConj_iff.1 ((mem_RA_iff_isConj r).1 hr)
    exact (Nat.card_congr ((centralizerConjEquiv h hh).trans centralizerLamW0Equiv).toEquiv).trans
      natCard_P1
  rcases hy with hy | hy
  · exact hRA hy
  · have hr : cV0 * y ∈ RA := hy
    exact (Nat.card_congr (MulEquiv.subgroupCongr (centralizer_cV0_mul y)).toEquiv).symm.trans
      (hRA hr)

theorem centralizer_equiv_apply_ne_cV0
    {y y' : vStab cv0} (hy : y ∈ RB) (hy' : y' ∈ RA ∪ RB)
    (θ : Subgroup.centralizer {y} ≃* Subgroup.centralizer {y'}) :
    θ ⟨y, mem_centralizer_singleton_self y⟩ ≠ ⟨cV0, cV0_mem_centralizer y'⟩ := fun h =>
  pCoreComm_ne_zpowers_cV0 hy' ((commutator_pCore_eq_of_equiv θ (pCoreComm_of_mem_RB hy)).trans
    (congrArg Subgroup.zpowers h))

theorem not_isConj_of_mem_RB
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hswap : ∀ y : vStab cv0, IsConj d (ψ.symm y : G) → y ≠ cV0 →
      ∃ (y' : vStab cv0) (θ : Subgroup.centralizer {y} ≃* Subgroup.centralizer {y'}),
        θ ⟨y, mem_centralizer_singleton_self y⟩ = ⟨cV0, cV0_mem_centralizer y'⟩ ∧
        θ ⟨cV0, cV0_mem_centralizer y⟩ = ⟨y', mem_centralizer_singleton_self y'⟩)
    (hHC2 : ∀ y : vStab cv0, orderOf y = 2 → y ≠ cV0 →
      2 ^ 38 ∣ Nat.card (Subgroup.centralizer {y}) → y ∈ RA ∪ RB)
    {y : vStab cv0} (hy : y ∈ RB) : ¬ IsConj d (ψ.symm y : G) := by
  intro hconj
  obtain ⟨y', θ, hθy, hθc⟩ := hswap y hconj (ne_cV0_of_mem_RB hy)
  have hord : orderOf y' = 2 :=
    (Subgroup.orderOf_mk y' (mem_centralizer_singleton_self y')).symm.trans
      ((congrArg orderOf hθc.symm).trans ((MulEquiv.orderOf_eq θ _).trans
        ((Subgroup.orderOf_mk cV0 _).trans orderOf_cV0)))
  have hne : y' ≠ cV0 := fun hy'c => ne_cV0_of_mem_RB hy
    (congrArg Subtype.val (θ.injective (hθy.trans ((Subtype.ext hy'c.symm).trans hθc.symm))))
  have hcard : Nat.card (Subgroup.centralizer {y'}) = 77148607752437760 :=
    (Nat.card_congr θ.toEquiv).symm.trans (natCard_centralizer_of_mem_RA_or_RB (Or.inr hy))
  have hdvd : 2 ^ 38 ∣ Nat.card (Subgroup.centralizer {y'}) := by
    rw [hcard]
    exact ⟨280665, by norm_num⟩
  exact centralizer_equiv_apply_ne_cV0 hy (hHC2 y' hord hne hdvd) θ hθy

theorem not_mem_dH_of_mem_RB
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0)
    (hHC2 : ∀ y : vStab cv0, orderOf y = 2 → y ≠ cV0 →
      2 ^ 38 ∣ Nat.card (Subgroup.centralizer {y}) → y ∈ RA ∪ RB)
    {y : vStab cv0} (hy : y ∈ RB) : y ∉ dH ψ :=
  not_isConj_of_mem_RB ψ (fun z hz hne => by
    have h := exists_swap_cV0 ψ hψ ((mem_dH_iff ψ z).2 hz) hne
    exact ⟨h.choose, h.choose_spec.2.2.choose,
      Subtype.ext h.choose_spec.2.2.choose_spec.2.1, Subtype.ext h.choose_spec.2.2.choose_spec.1⟩)
    hHC2 hy

theorem not_mem_dH_of_mem_RB'
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {y : vStab cv0} (hy : y ∈ RB) :
    y ∉ dH ψ :=
  not_mem_dH_of_mem_RB ψ hψ (fun _ h2 hc hd => mem_RA_or_RB_of_two_part h2 hc hd) hy

theorem RB_inter_dH_eq_empty
    {G : Type*} [Group G] {d : G}
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) : RB ∩ dH ψ = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ h => not_mem_dH_of_mem_RB' ψ hψ h.1 h.2

end CFSG.Monster.B.GSide

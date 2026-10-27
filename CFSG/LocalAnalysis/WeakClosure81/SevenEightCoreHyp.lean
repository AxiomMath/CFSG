module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCorePre
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]


private theorem seven_eight_core_hyp_deltaSet_ne_one {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H J φ)
    {v : G} (hv : v ∈ V) (hvJ : v ∉ J)
    {a : Q} (ha : a ∈ deltaSet (barSub H φ (pCoreOf 2 L))
      (φ ⟨v, h.omega_le V h.mem hv⟩)) : a ≠ 1 := by
  rcases ha with ⟨b, -, rfl⟩
  intro h1
  have hv1 : φ ⟨v, h.omega_le V h.mem hv⟩ = 1 := by
    calc φ ⟨v, h.omega_le V h.mem hv⟩ =
          b⁻¹ * (b * φ ⟨v, h.omega_le V h.mem hv⟩ * b⁻¹) * b := by group
      _ = b⁻¹ * 1 * b := by rw [h1]
      _ = 1 := by group
  exact hvJ ((hφ.ker_iff ⟨v, h.omega_le V h.mem hv⟩).mp hv1)

private theorem seven_eight_core_hyp_phi_mul_inv {H J : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {v : G} {a a' : Q} {x y : G}
    {hxH : x * v * x⁻¹ ∈ H} {hyH : y * v * y⁻¹ ∈ H}
    (hx : a = φ ⟨x * v * x⁻¹, hxH⟩) (hy : a' = φ ⟨y * v * y⁻¹, hyH⟩)
    (hprod : (x * v * x⁻¹)⁻¹ * (y * v * y⁻¹) ∈ H) :
    φ ⟨(x * v * x⁻¹)⁻¹ * (y * v * y⁻¹), hprod⟩ = a⁻¹ * a' := by
  rw [show (⟨(x * v * x⁻¹)⁻¹ * (y * v * y⁻¹), hprod⟩ : ↥H) =
      ⟨x * v * x⁻¹, hxH⟩⁻¹ * ⟨y * v * y⁻¹, hyH⟩ from Subtype.ext rfl,
    map_mul, map_inv, hx, hy]

theorem Hyp78.commute_of_mem_commutator_zpowers_deltaSet {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {v : G} (hv : v ∈ V) (hvJ : v ∉ J) {Xb : Subgroup Q}
    (hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hXp : IsPGroup p Xb) (hexp : ∀ x ∈ Xb, x ^ p = 1)
    (hne : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      ⁅Xb, Subgroup.zpowers a⁆ ≠ ⊥) :
    ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      ∀ a' ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩), a ≠ a' →
        ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, a' * m = m * a' := by
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  haveI : (J.subgroupOf (barPre H φ Xb)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((barPre_le H φ Xb).trans (le_normalizer_of_subgroupOf_normal hJH h.jnormal))
  intro a ha a' ha' hane m hm
  obtain ⟨x, hxcore, hwH, haeq⟩ := Hyp78.exists_mem_pCoreOf_of_mem_deltaSet h hv ha
  obtain ⟨y, hycore, hw'H, ha'eq⟩ := Hyp78.exists_mem_pCoreOf_of_mem_deltaSet h hv ha'
  have hwJ : x * v * x⁻¹ ∉ J := fun hJ =>
    seven_eight_core_hyp_deltaSet_ne_one h hφ hv hvJ ha
      (by rw [haeq, (hφ.ker_iff ⟨x * v * x⁻¹, hwH⟩).mpr hJ])
  have hw'J : y * v * y⁻¹ ∉ J := fun hJ =>
    seven_eight_core_hyp_deltaSet_ne_one h hφ hv hvJ ha'
      (by rw [ha'eq, (hφ.ker_iff ⟨y * v * y⁻¹, hw'H⟩).mpr hJ])
  have hwU : x * v * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group]
  have hw'U' : y * v * y⁻¹ ∈ conjSubgroup V y⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rwa [show y⁻¹ * (y * v * y⁻¹) * (y⁻¹)⁻¹ = v by group]
  obtain ⟨hUom, -⟩ := Hyp78.conjSubgroup_inv_mem_omegaSet h hxcore
  obtain ⟨hU'om, -⟩ := Hyp78.conjSubgroup_inv_mem_omegaSet h hycore
  have hprodH : (x * v * x⁻¹)⁻¹ * (y * v * y⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem hwH) hw'H
  have hprod'H : (y * v * y⁻¹)⁻¹ * (x * v * x⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem hw'H) hwH
  have hxy : (x * v * x⁻¹)⁻¹ * (y * v * y⁻¹) ∉ J := by
    intro hJ
    exact hane (by
      have h1 : a⁻¹ * a' = 1 := by
        rw [← seven_eight_core_hyp_phi_mul_inv hφ haeq ha'eq hprodH]
        exact (hφ.ker_iff ⟨_, hprodH⟩).mpr hJ
      exact inv_mul_eq_one.mp h1)
  have hxy' : (y * v * y⁻¹)⁻¹ * (x * v * x⁻¹) ∉ J := by
    intro hJ
    exact hane (by
      have h1 : a'⁻¹ * a = 1 := by
        rw [← seven_eight_core_hyp_phi_mul_inv hφ ha'eq haeq hprod'H]
        exact (hφ.ker_iff ⟨_, hprod'H⟩).mpr hJ
      exact (inv_mul_eq_one.mp h1).symm)
  have hwD : x * v * x⁻¹ ∈ dSetIn V H E J (conjSubgroup V x⁻¹ ⊔ conjSubgroup V y⁻¹) := by
    exact ⟨conjSubgroup V x⁻¹, hUom, le_sup_of_le_left le_sup_left, hwU, hwJ⟩
  have h76 := Hyp78.hyp76_sup h hV2 hφ hv hvJ hXL hp hp2 hXp hexp hne hxcore hycore hxy
  have hcent := h76.centralizes_commutator (U := conjSubgroup V y⁻¹) hU'om
    (le_sup_of_le_left le_sup_right)
    (d := y * v * y⁻¹) (d' := x * v * x⁻¹) hw'U' hw'J hwD hxy'
  have hle : ⁅Xb, Subgroup.zpowers a⁆ ≤ Subgroup.centralizer ({a'} : Set Q) := by
    refine Subgroup.commutator_le.mpr ?_
    intro q hq r hr
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst b
    have hqbar : q ∈ barSub H φ (barPre H φ Xb) := by
      rwa [barSub_barPre hφ Xb]
    obtain ⟨k, hkX, hkφ⟩ := mem_barSub.mp hqbar
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    set YH : ↥H := ⁅k, (⟨x * v * x⁻¹, hwH⟩ : ↥H) ^ n⁆ with hYH
    have hYHcoe : (YH : G) = ⁅(k : G), (x * v * x⁻¹) ^ n⁆ := by
      change H.subtype YH = ⁅(k : G), (x * v * x⁻¹) ^ n⁆
      rw [hYH, map_commutatorElement H.subtype, map_zpow H.subtype]
      rfl
    have hy_mem : (YH : G) ∈ ⁅barPre H φ Xb, Subgroup.zpowers (x * v * x⁻¹)⁆ := by
      rw [hYHcoe]
      exact Subgroup.commutator_mem_commutator hkX
        (Subgroup.zpow_mem_zpowers (x * v * x⁻¹) n)
    have hcomm_y := hcent (y * v * y⁻¹) hw'U' (YH : G) hy_mem
    have hphi_Y : φ YH = ⁅q, a ^ n⁆ := by
      rw [hYH, map_commutatorElement, map_zpow, hkφ, ← haeq]
    calc a' * ⁅q, a ^ n⁆ = a' * φ YH := by rw [hphi_Y]
      _ = φ ⟨y * v * y⁻¹, hw'H⟩ * φ YH := by rw [← ha'eq]
      _ = φ (⟨y * v * y⁻¹, hw'H⟩ * YH) :=
            (map_mul φ ⟨y * v * y⁻¹, hw'H⟩ YH).symm
      _ = φ (YH * ⟨y * v * y⁻¹, hw'H⟩) := by
            rw [show (⟨y * v * y⁻¹, hw'H⟩ : ↥H) * YH =
              YH * ⟨y * v * y⁻¹, hw'H⟩ from Subtype.ext hcomm_y]
      _ = φ YH * φ ⟨y * v * y⁻¹, hw'H⟩ := map_mul φ YH ⟨y * v * y⁻¹, hw'H⟩
      _ = ⁅q, a ^ n⁆ * a' := by rw [hphi_Y, ha'eq]
  exact (Subgroup.mem_centralizer_iff.mp (hle hm)) a' (Set.mem_singleton a')

theorem Hyp78.inf_commutator_zpowers_eq_bot {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {v : G} (hv : v ∈ V) (hvJ : v ∉ J) {Xb : Subgroup Q}
    (hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hXp : IsPGroup p Xb) (hexp : ∀ x ∈ Xb, x ^ p = 1)
    (hne : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      ⁅Xb, Subgroup.zpowers a⁆ ≠ ⊥) :
    ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      ∀ a' ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩), a ≠ a' →
        ⁅Xb, Subgroup.zpowers a⁆ ⊓ ⁅Xb, Subgroup.zpowers a'⁆ = ⊥ := by
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  haveI : (J.subgroupOf (barPre H φ Xb)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      ((barPre_le H φ Xb).trans (le_normalizer_of_subgroupOf_normal hJH h.jnormal))
  intro a ha a' ha' hane
  obtain ⟨x, hxcore, hwH, haeq⟩ := Hyp78.exists_mem_pCoreOf_of_mem_deltaSet h hv ha
  obtain ⟨y, hycore, hw'H, ha'eq⟩ := Hyp78.exists_mem_pCoreOf_of_mem_deltaSet h hv ha'
  have hwJ : x * v * x⁻¹ ∉ J := fun hJ =>
    seven_eight_core_hyp_deltaSet_ne_one h hφ hv hvJ ha
      (by rw [haeq, (hφ.ker_iff ⟨x * v * x⁻¹, hwH⟩).mpr hJ])
  have hw'J : y * v * y⁻¹ ∉ J := fun hJ =>
    seven_eight_core_hyp_deltaSet_ne_one h hφ hv hvJ ha'
      (by rw [ha'eq, (hφ.ker_iff ⟨y * v * y⁻¹, hw'H⟩).mpr hJ])
  have hprodH : (x * v * x⁻¹)⁻¹ * (y * v * y⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem hwH) hw'H
  have hprod'H : (y * v * y⁻¹)⁻¹ * (x * v * x⁻¹) ∈ H :=
    H.mul_mem (H.inv_mem hw'H) hwH
  have hxy : (x * v * x⁻¹)⁻¹ * (y * v * y⁻¹) ∉ J := by
    intro hJ
    exact hane (by
      have h1 : a⁻¹ * a' = 1 := by
        rw [← seven_eight_core_hyp_phi_mul_inv hφ haeq ha'eq hprodH]
        exact (hφ.ker_iff ⟨_, hprodH⟩).mpr hJ
      exact inv_mul_eq_one.mp h1)
  have hwU : x * v * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group]
  have hw'U' : y * v * y⁻¹ ∈ conjSubgroup V y⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rwa [show y⁻¹ * (y * v * y⁻¹) * (y⁻¹)⁻¹ = v by group]
  obtain ⟨hUom, -⟩ := Hyp78.conjSubgroup_inv_mem_omegaSet h hxcore
  obtain ⟨hU'om, -⟩ := Hyp78.conjSubgroup_inv_mem_omegaSet h hycore
  have hwD : x * v * x⁻¹ ∈ dSetIn V H E J (conjSubgroup V x⁻¹ ⊔ conjSubgroup V y⁻¹) :=
    ⟨conjSubgroup V x⁻¹, hUom, le_sup_of_le_left le_sup_left, hwU, hwJ⟩
  have hw'D : y * v * y⁻¹ ∈ dSetIn V H E J (conjSubgroup V x⁻¹ ⊔ conjSubgroup V y⁻¹) :=
    ⟨conjSubgroup V y⁻¹, hU'om, le_sup_of_le_left le_sup_right, hw'U', hw'J⟩
  have h76 := Hyp78.hyp76_sup h hV2 hφ hv hvJ hXL hp hp2 hXp hexp hne hxcore hycore hxy
  have hInterJ := h76.inf_iSup_commModJ_le h.oddCore hwD
  have hle_sup : commModJ (barPre H φ Xb) J (y * v * y⁻¹) ≤
      ⨆ d' ∈ dSetIn V H E J (conjSubgroup V x⁻¹ ⊔ conjSubgroup V y⁻¹),
        ⨆ (_ : (x * v * x⁻¹)⁻¹ * d' ∉ J), commModJ (barPre H φ Xb) J d' :=
    le_iSup₂_of_le (y * v * y⁻¹) hw'D (le_iSup_of_le hxy le_rfl)
  have hInterJ' : commModJ (barPre H φ Xb) J (x * v * x⁻¹) ⊓
      commModJ (barPre H φ Xb) J (y * v * y⁻¹) ≤ J :=
    (inf_le_inf_left _ hle_sup).trans hInterJ
  rw [eq_bot_iff]
  intro m hm
  obtain ⟨k, hkφ⟩ := hφ.surjective m
  have hkpre : (k : G) ∈ barPre H φ ⁅Xb, Subgroup.zpowers (φ ⟨x * v * x⁻¹, hwH⟩)⁆ := by
    refine mem_barPre.mpr ⟨k.2, ?_⟩
    rw [show (⟨(k : G), k.2⟩ : ↥H) = k from Subtype.ext rfl, hkφ, ← haeq]
    exact hm.1
  have hkpre' : (k : G) ∈ barPre H φ ⁅Xb, Subgroup.zpowers (φ ⟨y * v * y⁻¹, hw'H⟩)⁆ := by
    refine mem_barPre.mpr ⟨k.2, ?_⟩
    rw [show (⟨(k : G), k.2⟩ : ↥H) = k from Subtype.ext rfl, hkφ, ← ha'eq]
    exact hm.2
  have hkJ : (k : G) ∈ J := hInterJ' ⟨
    barPre_commutator_zpowers_le hφ Xb hwH hkpre,
    barPre_commutator_zpowers_le hφ Xb hw'H hkpre'⟩
  rw [Subgroup.mem_bot, ← hkφ, (hφ.ker_iff k).mpr hkJ]

theorem Hyp78.card_commutator_zpowers_eq {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {v : G} (hv : v ∈ V) (hvJ : v ∉ J) {Xb : Subgroup Q}
    (hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hXp : IsPGroup p Xb) (hexp : ∀ x ∈ Xb, x ^ p = 1)
    {a : Q} (ha : a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩))
    (hne : ⁅Xb, Subgroup.zpowers a⁆ ≠ ⊥)
    (hab : ∀ m ∈ ⁅Xb, Subgroup.zpowers a⁆, ∀ m' ∈ ⁅Xb, Subgroup.zpowers a⁆, m * m' = m' * m) :
    Nat.card ↥(⁅Xb, Subgroup.zpowers a⁆ : Subgroup Q) = p := by
  set M : Subgroup Q := ⁅Xb, Subgroup.zpowers a⁆ with hM
  have habM : ∀ m ∈ M, ∀ m' ∈ M, m * m' = m' * m := hab
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  obtain ⟨x, hxcore, hwH, haeq⟩ := Hyp78.exists_mem_pCoreOf_of_mem_deltaSet h hv ha
  have hF := Hyp78.sevenEightFrame h hV2 hφ hv hvJ
  have ha2 : a * a = 1 := (hF.mul_self_and_mem_of_mem_deltaSet ha).1
  have haXb : a ∈ Subgroup.normalizer (Xb : Set Q) :=
    hXL (hF.mul_self_and_mem_of_mem_deltaSet ha).2
  have ha1 : a ≠ 1 := seven_eight_core_hyp_deltaSet_ne_one h hφ hv hvJ ha
  have hwJ : x * v * x⁻¹ ∉ J := fun hJ =>
    ha1 (by rw [haeq, (hφ.ker_iff ⟨x * v * x⁻¹, hwH⟩).mpr hJ])
  have hwU : x * v * x⁻¹ ∈ conjSubgroup V x⁻¹ := by
    rw [mem_conjSubgroup_iff]
    rwa [show x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v by group]
  obtain ⟨hUom, -⟩ := Hyp78.conjSubgroup_inv_mem_omegaSet h hxcore
  have hMX : M ≤ Xb := commutator_zpowers_le haXb
  have hoddM : Odd (Nat.card ↥M) := by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hXp.to_le hMX)
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  have hMS : M ≤ ⁅M, Subgroup.zpowers a⁆ := by
    intro m hm
    have hEven : Even (Nat.card ↥M + 1) := by
      obtain ⟨k, hk⟩ := hoddM
      exact ⟨k + 1, by rw [hk]; ring⟩
    set e : ℕ := (Nat.card ↥M + 1) / 2 with he
    set m' : Q := m ^ e with hm'
    have hm'M : m' ∈ M := Subgroup.pow_mem _ hm e
    have hm_card : (m : Q) ^ Nat.card ↥M = 1 := by
      have h := map_pow M.subtype (⟨m, hm⟩ : ↥M) (Nat.card ↥M)
      rw [pow_card_eq_one' (G := ↥M) (x := (⟨m, hm⟩ : ↥M)), map_one] at h
      exact h.symm
    have hmsq : m' * m' = m := by
      have hdiv : e * 2 = Nat.card ↥M + 1 :=
        Nat.div_mul_cancel (even_iff_two_dvd.mp hEven)
      calc m' * m' = (m ^ e) * (m ^ e) := by rw [hm']
        _ = (m ^ e) ^ 2 := (pow_two (m ^ e)).symm
        _ = m ^ (e * 2) := by rw [pow_mul]
        _ = m ^ (Nat.card ↥M + 1) := by rw [hdiv]
        _ = m ^ Nat.card ↥M * m := pow_succ m _
        _ = 1 * m := by rw [hm_card]
        _ = m := one_mul m
    have hcomm : ⁅m', a⁆ = m := by
      rw [commutatorElement_def]
      rw [show m' * a * m'⁻¹ * a⁻¹ = m' * (a * m'⁻¹ * a⁻¹) by group,
        conj_eq_inv_of_mem_commutator_zpowers ha2 habM m'⁻¹ (Subgroup.inv_mem _ hm'M),
        inv_inv, hmsq]
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator hm'M (Subgroup.mem_zpowers a)
  change Nat.card ↥M = p
  set Xm : Subgroup G := barPre H φ M with hXm
  have hJXm : J ≤ Xm := le_barPre hJH hφ M
  have hXmH : Xm ≤ H := barPre_le H φ M
  have haeq' : a = φ ⟨x * v * x⁻¹, h.omega_le (conjSubgroup V x⁻¹) hUom hwU⟩ := by
    rw [haeq]
  have hAH : conjSubgroup V x⁻¹ ≤ H := h.omega_le _ hUom
  have hbarU : barSub H φ (conjSubgroup V x⁻¹) ≤ Subgroup.normalizer (M : Set Q) := by
    refine (Hyp78.barSub_le_zpowers_of_mem_omegaSet h hV2 hφ hUom hwU hwJ).trans ?_
    rw [← haeq']
    exact Subgroup.normalizer_commutator_ge_right Xb (Subgroup.zpowers a)
  have hAXm : conjSubgroup V x⁻¹ ≤ Subgroup.normalizer (Xm : Set G) :=
    le_normalizer_barPre hφ hAH hbarU
  have hxa : Xm ≤ ⁅Xm, conjSubgroup V x⁻¹⁆ ⊔ J := by
    have hpre_mono : barPre H φ M ≤ barPre H φ ⁅M, Subgroup.zpowers a⁆ := by
      intro g hg
      obtain ⟨hgH, hgM⟩ := mem_barPre.mp hg
      exact mem_barPre.mpr ⟨hgH, hMS hgM⟩
    have hbar : barPre H φ ⁅M, Subgroup.zpowers a⁆ ≤
        commModJ (barPre H φ M) J (x * v * x⁻¹) := by
      have h := barPre_commutator_zpowers_le hφ M hwH
      rwa [← haeq] at h
    calc Xm = barPre H φ M := rfl
      _ ≤ barPre H φ ⁅M, Subgroup.zpowers a⁆ := hpre_mono
      _ ≤ commModJ (barPre H φ M) J (x * v * x⁻¹) := hbar
      _ ≤ ⁅Xm, conjSubgroup V x⁻¹⁆ ⊔ J := by
            rw [commModJ]
            exact sup_le ((Subgroup.commutator_mono le_rfl
              (Subgroup.zpowers_le.mpr hwU)).trans le_sup_left) le_sup_right
  have hcommJ : ∀ x ∈ Xm, ∀ y ∈ Xm, ⁅x, y⁆ ∈ J := by
    intro g hg g' hg'
    obtain ⟨hgH, hgM⟩ := mem_barPre.mp hg
    obtain ⟨hg'H, hg'M⟩ := mem_barPre.mp hg'
    have hcomm1 : ⁅φ ⟨g, hgH⟩, φ ⟨g', hg'H⟩⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (habM _ hgM _ hg'M)
    refine (hφ.ker_iff (⟨⁅g, g'⁆, H.mul_mem (H.mul_mem (H.mul_mem hgH hg'H)
      (H.inv_mem hgH)) (H.inv_mem hg'H)⟩ : ↥H)).mp ?_
    change φ ⁅(⟨g, hgH⟩ : ↥H), (⟨g', hg'H⟩ : ↥H)⁆ = 1
    rw [map_commutatorElement]
    exact hcomm1
  have hfaith : ∀ g ∈ conjSubgroup V x⁻¹,
      (∀ y ∈ barPre H φ M, ⁅g, y⁆ ∈ J) → g ∈ J :=
    Hyp78.faithful_of_mem_omegaSet h hV2 hφ hUom hwU hwJ (Xb := M) (by
      rw [← haeq']
      intro hbot
      exact hne (bot_unique (hMS.trans (le_of_eq hbot))))
  have hexp' : ∀ g ∈ Xm, g ^ p ∈ J := by
    intro g hg
    obtain ⟨hgH, hgM⟩ := mem_barPre.mp hg
    have hpow : (φ ⟨g, hgH⟩) ^ p = 1 := hexp _ (hMX hgM)
    have hker : ((⟨g, hgH⟩ : ↥H) ^ p : G) ∈ J :=
      (hφ.ker_iff _).mp (by rw [map_pow, hpow])
    simpa using hker
  have hcl : ∀ g ∈ Xm, ∀ g' ∈ Xm, ∀ g'' ∈ Xm, ⁅⁅g, g'⁆, g''⁆ ∈ J := by
    have hHnormJ : H ≤ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_subgroupOf_normal hJH h.jnormal
    have hJHcomm : ⁅J, H⁆ ≤ J := (Subgroup.le_normalizer_iff_commutator_le_left).mp hHnormJ
    intro g hg g' hg' g'' hg''
    have hg''H : g'' ∈ H := (mem_barPre.mp hg'').1
    exact hJHcomm (Subgroup.commutator_mem_commutator (hcommJ g hg g' hg') hg''H)
  have hJU : J.relIndex (conjSubgroup V x⁻¹) = 2 :=
    Hyp78.relIndex_eq_two_of_mem_omegaSet h hV2 hUom
  have hres := seven_six_three_member h.elemAbelian h.ti hp hp2 h.abelian h.le h.normal
    h.omega_le h.pcore_le h.jnormal h.iSub_le hUom hJU hJXm hXmH hAXm hxa hfaith hexp' hcl
  rw [hXm, relIndex_barPre hJH hφ M] at hres
  rcases hres with h | ⟨-, g, hg, g', hg', hgg'⟩
  · exact h
  · exact absurd (hcommJ g hg g' hg') hgg'

end CFSG.LocalAnalysis.WeakClosure81

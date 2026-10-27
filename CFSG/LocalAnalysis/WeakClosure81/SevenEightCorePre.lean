module

public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeAmb

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem seven_eight_core_pre_zpow_eq_one_or_self {Q : Type} [Group Q] {x : Q}
    (hx : x * x = 1) (n : ℤ) : x ^ n = 1 ∨ x ^ n = x := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
    rw [h2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul]
    have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
    rw [h2, one_zpow, zpow_one, one_mul]

private theorem seven_eight_core_pre_relIndex_conjSubgroup (A B : Subgroup G) (k : G) :
    (conjSubgroup A k).relIndex (conjSubgroup B k) = A.relIndex B := by
  simp only [CFSG.Quasithin.conjSubgroup]
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj k⁻¹).injective

private theorem seven_eight_core_pre_zpowers_le_centralizer {H J : Subgroup G} {Q : Type}
    [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H J φ) {Xb : Subgroup Q} {g : G} (hgH : g ∈ H)
    (hcomm : ∀ z ∈ barPre H φ Xb, ⁅g, z⁆ ∈ J) :
    Subgroup.zpowers (φ ⟨g, hgH⟩) ≤ Subgroup.centralizer (Xb : Set Q) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨k, hkq⟩ := hφ.surjective q
  have hkbar : (k : G) ∈ barPre H φ Xb :=
    mem_barPre.mpr ⟨k.2, by rw [hkq]; exact hq⟩
  have hcommJ : ⁅g, (k : G)⁆ ∈ J := hcomm (k : G) hkbar
  have hker : φ ⁅(⟨g, hgH⟩ : ↥H), k⁆ = 1 := by
    apply (hφ.ker_iff ⁅(⟨g, hgH⟩ : ↥H), k⁆).mpr
    have hcoe : ((⁅(⟨g, hgH⟩ : ↥H), k⁆ : ↥H) : G) = ⁅g, (k : G)⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe]
    exact hcommJ
  have h1 : ⁅φ ⟨g, hgH⟩, φ k⁆ = 1 := by
    rw [← map_commutatorElement φ (⟨g, hgH⟩ : ↥H) k]
    exact hker
  rw [hkq] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

private theorem seven_eight_core_pre_inv_commutator_self {Q : Type} [Group Q] {a x : Q}
    (ha : a * a = 1) : a * ⁅x, a⁆ * a⁻¹ = ⁅x, a⁆⁻¹ := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [commutatorElement_def, hai]
  have hL : a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ := by
    rw [show a * (x * a * x⁻¹ * a) * a = a * x * a * x⁻¹ * (a * a) by group, ha, mul_one]
  have hR : (x * a * x⁻¹ * a)⁻¹ = a * x * a * x⁻¹ := by
    rw [show (x * a * x⁻¹ * a)⁻¹ = a⁻¹ * x * a⁻¹ * x⁻¹ by group, hai]
  rw [hL, hR]

private theorem seven_eight_core_pre_commutator_zpowers_eq_bot_of_centralizes {Q : Type} [Group Q]
    {Xb : Subgroup Q} {c : Q} (hc : c ∈ Subgroup.centralizer (Xb : Set Q)) :
    ⁅Xb, Subgroup.zpowers c⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.zpowers_le]
  exact hc

theorem hyp76_sup_of_commute {V H E J U U' X : Subgroup G} {p : ℕ} [(J.subgroupOf X).Normal]
    (h : Hyp73 V H E J) (hp : p.Prime) (hp2 : p ≠ 2) (hU : U ∈ omegaSet V H E)
    (hU' : U' ∈ omegaSet V H E) (hUU' : ∀ u ∈ U, ∀ u' ∈ U', u * u' = u' * u)
    (hJX : J ≤ X) (hXH : X ≤ H) (hAX : U ⊔ U' ≤ Subgroup.normalizer (X : Set G))
    (hfaith : ∀ a ∈ U ⊔ U', (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J) (hexp : ∀ x ∈ X, x ^ p ∈ J) :
    Hyp76 V H E J (U ⊔ U') X := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg := isPGroup_quotient_of_exp (J := J) (Y := X) hexp
  refine ⟨h.elemAbelian, h.ti, h.abelian, h.le, h.normal, h.omega_le, h.pcore_le, h.jnormal,
    h.iSub_le, hJX, hXH, hAX, ?_, ?_, hfaith, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
    have h1 : J.relIndex X = Nat.card (↥X ⧸ J.subgroupOf X) := Subgroup.index_eq_card _
    rw [h1, hn]
    exact (hp.odd_of_ne_two hp2).pow
  · exact hpg.isNilpotent
  · refine le_antisymm ?_ (iSup₂_le fun W _ => iSup_le fun h => h)
    refine sup_le ?_ ?_
    · exact le_iSup₂_of_le U hU (le_iSup_of_le le_sup_left le_rfl)
    · exact le_iSup₂_of_le U' hU' (le_iSup_of_le le_sup_right le_rfl)
  · have hUp : IsPGroup 2 U := (isElemAbelian_of_mem_omegaSet h.elemAbelian hU).isPGroup
    have hU'p : IsPGroup 2 U' := (isElemAbelian_of_mem_omegaSet h.elemAbelian hU').isPGroup
    refine IsPGroup.to_sup_of_normal_right' hUp hU'p ?_
    have hcent : U ≤ Subgroup.centralizer (U' : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hUU' u hu z hz).symm
    exact hcent.trans (Subgroup.centralizer_le_normalizer (U' : Set G))

theorem Hyp78.exists_mem_pCoreOf_of_mem_deltaSet {V H E J L : Subgroup G}
    (h : Hyp78 V H E J L) {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q} {v : G} (hv : v ∈ V)
    {a : Q} (ha : a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩)) :
    ∃ x ∈ pCoreOf 2 L, ∃ hw : x * v * x⁻¹ ∈ H, a = φ ⟨x * v * x⁻¹, hw⟩ := by
  obtain ⟨y, hy, rfl⟩ := ha
  obtain ⟨k, hkcore, hkφ⟩ := mem_barSub.mp hy
  refine ⟨(k : G), hkcore,
    H.mul_mem (H.mul_mem k.2 (h.omega_le V h.mem hv)) (H.inv_mem k.2), ?_⟩
  rw [← hkφ]
  rw [show (⟨(k : G) * v * (k : G)⁻¹,
      H.mul_mem (H.mul_mem k.2 (h.omega_le V h.mem hv)) (H.inv_mem k.2)⟩ : ↥H) =
      k * ⟨v, h.omega_le V h.mem hv⟩ * k⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]

theorem Hyp78.conjSubgroup_inv_mem_omegaSet {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    {x : G} (hx : x ∈ pCoreOf 2 L) :
    conjSubgroup V x⁻¹ ∈ omegaSet V H E ∧ conjSubgroup V x⁻¹ ≤ L := by
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLleH : L ≤ H := h.le_kSub.trans hKleH
  have hxL : x ∈ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hx
  have hxH : x ∈ H := hLleH hxL
  refine ⟨conjSubgroup_mem_omegaSet h.le h.normal h.mem (H.inv_mem hxH), ?_⟩
  intro g hg
  have hmemV : x⁻¹ * g * x ∈ V := by
    have hmem := mem_conjSubgroup_iff.mp hg
    simpa [inv_inv] using hmem
  have hmemL : x⁻¹ * g * x ∈ L := h.left_le hmemV
  rw [show g = x * (x⁻¹ * g * x) * x⁻¹ by group]
  exact L.mul_mem (L.mul_mem hxL hmemL) (L.inv_mem hxL)

theorem Hyp78.relIndex_eq_two_of_mem_omegaSet {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {U : Subgroup G} (hU : U ∈ omegaSet V H E) :
    J.relIndex U = 2 := by
  obtain ⟨k, hkK, rfl⟩ := h.transitive U hU
  have hKleH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hkH : k ∈ H := hKleH hkK
  have hJleH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJleH h.jnormal
  have hJk : conjSubgroup J k = J :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (hJnormH hkH)
  have hstep : (conjSubgroup J k).relIndex (conjSubgroup V k) = J.relIndex V :=
    seven_eight_core_pre_relIndex_conjSubgroup J V k
  rwa [hJk, hV2] at hstep

theorem Hyp78.barSub_le_zpowers_of_mem_omegaSet {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H J φ)
    {U : Subgroup G} (hU : U ∈ omegaSet V H E) {u : G} (hu : u ∈ U) (huJ : u ∉ J) :
    barSub H φ U ≤ Subgroup.zpowers (φ ⟨u, h.omega_le U hU hu⟩) := by
  have huH : u ∈ H := h.omega_le U hU hu
  have hUrel : J.relIndex U = 2 := h.relIndex_eq_two_of_mem_omegaSet hV2 hU
  intro q hq
  obtain ⟨g, hgU, rfl⟩ := mem_barSub.mp hq
  by_cases hgJ : (g : G) ∈ J
  · rw [Subgroup.mem_zpowers_iff]
    exact ⟨0, by rw [zpow_zero]; exact ((hφ.ker_iff g).mpr hgJ).symm⟩
  · have hmul := Subgroup.mul_mem_iff_of_index_two (H := J.subgroupOf U) hUrel
      (a := (⟨u, hu⟩ : ↥U)⁻¹) (b := (⟨(g : G), hgU⟩ : ↥U))
    have hiff : ((⟨u, hu⟩ : ↥U)⁻¹ ∈ J.subgroupOf U) ↔
        ((⟨(g : G), hgU⟩ : ↥U) ∈ J.subgroupOf U) := by
      constructor
      · intro hu'
        exact absurd (by
          have h1 : ((⟨u, hu⟩ : ↥U)⁻¹ : G) ∈ J := Subgroup.mem_subgroupOf.mp hu'
          have h2 : u⁻¹ ∈ J := by simpa using h1
          simpa using J.inv_mem h2) huJ
      · intro hg'
        exact absurd (Subgroup.mem_subgroupOf.mp hg') hgJ
    have hmem : (⟨u, hu⟩ : ↥U)⁻¹ * (⟨(g : G), hgU⟩ : ↥U) ∈ J.subgroupOf U := hmul.mpr hiff
    have hJu'g : u⁻¹ * (g : G) ∈ J := by
      have hcoe := Subgroup.mem_subgroupOf.mp hmem
      simpa using hcoe
    let uH : ↥H := ⟨u, huH⟩
    have hker : φ ((uH)⁻¹ * g) = 1 := by
      apply (hφ.ker_iff _).mpr
      simpa [uH] using hJu'g
    have hEq : φ g = φ uH := by
      rw [show g = uH * ((uH)⁻¹ * g) by group, map_mul, hker, mul_one]
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨1, by rw [zpow_one]; exact hEq.symm⟩

theorem Hyp78.faithful_of_mem_omegaSet {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H J φ)
    {U : Subgroup G} (hU : U ∈ omegaSet V H E) {u : G} (hu : u ∈ U) (huJ : u ∉ J)
    {Xb : Subgroup Q} (hne : ⁅Xb, Subgroup.zpowers (φ ⟨u, h.omega_le U hU hu⟩)⁆ ≠ ⊥) :
    ∀ g ∈ U, (∀ y ∈ barPre H φ Xb, ⁅g, y⁆ ∈ J) → g ∈ J := by
  intro g hgU hcomm
  by_contra hgJ
  have hgH : g ∈ H := h.omega_le U hU hgU
  let gH : ↥H := ⟨g, hgH⟩
  let uH : ↥H := ⟨u, h.omega_le U hU hu⟩
  have hle := h.barSub_le_zpowers_of_mem_omegaSet hV2 hφ hU hu huJ
  have hgbar : φ gH ∈ barSub H φ U := mem_barSub.mpr ⟨gH, hgU, rfl⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hle hgbar)
  have hu2 : (φ uH) * (φ uH) = 1 := by
    rw [← map_mul, show uH * uH = 1 from Subtype.ext
      (elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hU) hu), map_one]
  have hEq : φ gH = φ uH := by
    rcases seven_eight_core_pre_zpow_eq_one_or_self hu2 n with h1 | h1
    · exfalso
      exact hgJ ((hφ.ker_iff gH).mp (hn.symm.trans h1))
    · exact hn.symm.trans h1
  have hcent := seven_eight_core_pre_zpowers_le_centralizer hφ hgH hcomm
  have hbot : ⁅Xb, Subgroup.zpowers (φ uH)⁆ = ⊥ := by
    rw [← hEq]
    exact seven_eight_core_pre_commutator_zpowers_eq_bot_of_centralizes
      (hcent (Subgroup.mem_zpowers _))
  exact hne hbot

theorem barPre_commutator_zpowers_le {H J : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) (Xb : Subgroup Q) {w : G} (hw : w ∈ H) :
    barPre H φ ⁅Xb, Subgroup.zpowers (φ ⟨w, hw⟩)⁆ ≤ commModJ (barPre H φ Xb) J w := by
  let wH : ↥H := ⟨w, hw⟩
  have hsub : ⁅Xb, Subgroup.zpowers (φ wH)⁆ ≤
      barSub H φ ⁅barPre H φ Xb, Subgroup.zpowers w⁆ := by
    rw [Subgroup.commutator_le]
    intro q hq r hr
    have hq' : q ∈ barSub H φ (barPre H φ Xb) := by rwa [barSub_barPre hφ Xb]
    obtain ⟨k, hkX, hkφ⟩ := mem_barSub.mp hq'
    rw [Subgroup.mem_zpowers_iff] at hr
    obtain ⟨n, rfl⟩ := hr
    refine mem_barSub.mpr ⟨⁅k, wH ^ n⁆, ?_, ?_⟩
    · have hkbar : (k : G) ∈ barPre H φ Xb :=
        mem_barPre.mpr ⟨k.2, by show φ k ∈ Xb; rw [hkφ]; exact hq⟩
      have hwn : ((wH ^ n : ↥H) : G) ∈ Subgroup.zpowers w := by
        change w ^ n ∈ Subgroup.zpowers w
        exact Subgroup.zpow_mem_zpowers w n
      have hmem : ⁅(k : G), ((wH ^ n : ↥H) : G)⁆ ∈
          ⁅barPre H φ Xb, Subgroup.zpowers w⁆ :=
        Subgroup.commutator_mem_commutator hkbar hwn
      have hcoe : ((⁅k, wH ^ n⁆ : ↥H) : G) = ⁅(k : G), ((wH ^ n : ↥H) : G)⁆ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      rwa [hcoe]
    · rw [map_commutatorElement, map_zpow, hkφ]
  intro g hg
  obtain ⟨hgH, hgX⟩ := mem_barPre.mp hg
  have hgX' : φ ⟨g, hgH⟩ ∈ barSub H φ ⁅barPre H φ Xb, Subgroup.zpowers w⁆ := hsub hgX
  obtain ⟨k, hk, hkφ⟩ := mem_barSub.mp hgX'
  have hker : ((k⁻¹ * ⟨g, hgH⟩ : ↥H) : G) ∈ J :=
    (hφ.ker_iff (k⁻¹ * ⟨g, hgH⟩)).mp (by rw [map_mul, map_inv, hkφ]; group)
  rw [commModJ]
  rw [show g = (k : G) * (((k⁻¹ * ⟨g, hgH⟩ : ↥H)) : G) by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]; group]
  exact Subgroup.mul_mem_sup hk hker

theorem Hyp78.hyp76_sup {V H E J L : Subgroup G} (h : Hyp78 V H E J L)
    (hV2 : J.relIndex V = 2) {Q : Type} [Group Q] [Finite Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H J φ) {v : G} (hv : v ∈ V) (hvJ : v ∉ J) {Xb : Subgroup Q}
    (hXL : barSub H φ L ≤ Subgroup.normalizer (Xb : Set Q)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hXp : IsPGroup p Xb) (hexp : ∀ x ∈ Xb, x ^ p = 1)
    (hne : ∀ a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, h.omega_le V h.mem hv⟩),
      ⁅Xb, Subgroup.zpowers a⁆ ≠ ⊥)
    {x y : G} (hx : x ∈ pCoreOf 2 L) (hy : y ∈ pCoreOf 2 L)
    (hxy : (x * v * x⁻¹)⁻¹ * (y * v * y⁻¹) ∉ J) [(J.subgroupOf (barPre H φ Xb)).Normal] :
    Hyp76 V H E J (conjSubgroup V x⁻¹ ⊔ conjSubgroup V y⁻¹) (barPre H φ Xb) := by
  have hJH : J ≤ H := h.pcore_le.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
  have hKH : kSub V H E ≤ H := kSub_le_of_forall_le h.omega_le
  have hLH : L ≤ H := h.le_kSub.trans hKH
  have hJnormH : H ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_subgroupOf_normal hJH h.jnormal
  have hxL : x ∈ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hx
  have hyL : y ∈ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hy
  have hxH : x ∈ H := hLH hxL
  have hyH : y ∈ H := hLH hyL
  have hxinv : x⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hx
  have hyinv : y⁻¹ ∈ pCoreOf 2 L := (pCoreOf 2 L).inv_mem hy
  have hUmem : conjSubgroup V x⁻¹ ∈ omegaSet V H E :=
    (Hyp78.conjSubgroup_inv_mem_omegaSet h hx).1
  have hU'mem : conjSubgroup V y⁻¹ ∈ omegaSet V H E :=
    (Hyp78.conjSubgroup_inv_mem_omegaSet h hy).1
  have hUL : conjSubgroup V x⁻¹ ≤ L := (Hyp78.conjSubgroup_inv_mem_omegaSet h hx).2
  have hU'L : conjSubgroup V y⁻¹ ≤ L := (Hyp78.conjSubgroup_inv_mem_omegaSet h hy).2
  have hUU' : ∀ u ∈ conjSubgroup V x⁻¹, ∀ u' ∈ conjSubgroup V y⁻¹, u * u' = u' * u := by
    intro u hu u' hu'
    have hbot := seven_eight_commutator_conj_eq_bot h hxinv hyinv
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    exact ((Subgroup.mem_centralizer_iff.mp (hle hu)) u' hu').symm
  have hAX : conjSubgroup V x⁻¹ ⊔ conjSubgroup V y⁻¹ ≤
      Subgroup.normalizer ((barPre H φ Xb : Subgroup G) : Set G) :=
    sup_le (hUL.trans (le_normalizer_barPre hφ hLH hXL))
      (hU'L.trans (le_normalizer_barPre hφ hLH hXL))
  have hexpG : ∀ g ∈ barPre H φ Xb, g ^ p ∈ J := by
    intro g hg
    obtain ⟨hgH, hgX⟩ := mem_barPre.mp hg
    have hgpH : g ^ p ∈ H := H.pow_mem hgH p
    have hphi : φ ⟨g ^ p, hgpH⟩ = 1 := by
      rw [show (⟨g ^ p, hgpH⟩ : ↥H) = ⟨g, hgH⟩ ^ p from Subtype.ext rfl, map_pow]
      exact hexp _ hgX
    exact (hφ.ker_iff ⟨g ^ p, hgpH⟩).mp hphi
  have hVH : v ∈ H := h.omega_le V h.mem hv
  set w : G := x * v * x⁻¹ with hwdef
  set w' : G := y * v * y⁻¹ with hw'def
  have hwU : w ∈ conjSubgroup V x⁻¹ := by
    rw [mem_conjSubgroup_iff, hwdef, inv_inv]
    rw [show x⁻¹ * (x * v * x⁻¹) * x = v by group]
    exact hv
  have hw'U : w' ∈ conjSubgroup V y⁻¹ := by
    rw [mem_conjSubgroup_iff, hw'def, inv_inv]
    rw [show y⁻¹ * (y * v * y⁻¹) * y = v by group]
    exact hv
  have hwH : w ∈ H := (h.omega_le _ hUmem) hwU
  have hw'H : w' ∈ H := (h.omega_le _ hU'mem) hw'U
  have hwL : w ∈ L := hUL hwU
  have hw'L : w' ∈ L := hU'L hw'U
  have hwJ : w ∉ J := by
    intro hwJmem
    apply hvJ
    have hconj := (Subgroup.mem_normalizer_iff.mp (hJnormH (H.inv_mem hxH)) w).mp hwJmem
    rwa [inv_inv, show x⁻¹ * w * x = v by rw [hwdef]; group] at hconj
  have hw'J : w' ∉ J := by
    intro hw'Jmem
    apply hvJ
    have hconj := (Subgroup.mem_normalizer_iff.mp (hJnormH (H.inv_mem hyH)) w').mp hw'Jmem
    rwa [inv_inv, show y⁻¹ * w' * y = v by rw [hw'def]; group] at hconj
  set a : Q := φ ⟨w, hwH⟩ with hadef
  set a' : Q := φ ⟨w', hw'H⟩ with ha'def
  have haΔ : a ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩) := by
    rw [hadef]
    refine ⟨φ ⟨x, hxH⟩, mem_barSub.mpr ⟨⟨x, hxH⟩, hx, rfl⟩, ?_⟩
    show φ ⟨w, hwH⟩ = φ ⟨x, hxH⟩ * φ ⟨v, hVH⟩ * (φ ⟨x, hxH⟩)⁻¹
    rw [show (⟨w, hwH⟩ : ↥H) = ⟨x, hxH⟩ * ⟨v, hVH⟩ * ⟨x, hxH⟩⁻¹ from Subtype.ext hwdef,
      map_mul, map_mul, map_inv]
  have ha'Δ : a' ∈ deltaSet (barSub H φ (pCoreOf 2 L)) (φ ⟨v, hVH⟩) := by
    rw [ha'def]
    refine ⟨φ ⟨y, hyH⟩, mem_barSub.mpr ⟨⟨y, hyH⟩, hy, rfl⟩, ?_⟩
    show φ ⟨w', hw'H⟩ = φ ⟨y, hyH⟩ * φ ⟨v, hVH⟩ * (φ ⟨y, hyH⟩)⁻¹
    rw [show (⟨w', hw'H⟩ : ↥H) = ⟨y, hyH⟩ * ⟨v, hVH⟩ * ⟨y, hyH⟩⁻¹ from Subtype.ext hw'def,
      map_mul, map_mul, map_inv]
  have ha2 : a * a = 1 := by
    show φ ⟨w, hwH⟩ * φ ⟨w, hwH⟩ = 1
    rw [← map_mul, show (⟨w, hwH⟩ : ↥H) * ⟨w, hwH⟩ = 1 from Subtype.ext
      (elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hUmem) hwU), map_one]
  have ha'2 : a' * a' = 1 := by
    show φ ⟨w', hw'H⟩ * φ ⟨w', hw'H⟩ = 1
    rw [← map_mul, show (⟨w', hw'H⟩ : ↥H) * ⟨w', hw'H⟩ = 1 from Subtype.ext
      (elemAbelian_mul_self (isElemAbelian_of_mem_omegaSet h.elemAbelian hU'mem) hw'U), map_one]
  have hfaith : ∀ g ∈ conjSubgroup V x⁻¹ ⊔ conjSubgroup V y⁻¹,
      (∀ z ∈ barPre H φ Xb, ⁅g, z⁆ ∈ J) → g ∈ J := by
    intro g hgUU hcomm
    have hcentU : conjSubgroup V x⁻¹ ≤ Subgroup.normalizer (conjSubgroup V y⁻¹ : Set G) := by
      have hc : conjSubgroup V x⁻¹ ≤ Subgroup.centralizer (conjSubgroup V y⁻¹ : Set G) := by
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hUU' u hu z hz).symm
      exact hc.trans (Subgroup.centralizer_le_normalizer _)
    have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup V x⁻¹)
      (conjSubgroup V y⁻¹) hcentU
    have hgmem : g ∈ (conjSubgroup V x⁻¹ : Set G) * (conjSubgroup V y⁻¹ : Set G) := by
      rw [← hcoe]; exact hgUU
    obtain ⟨u, hu, u', hu', hgu⟩ := Set.mem_mul.mp hgmem
    rw [← hgu] at hcomm ⊢
    have huH : u ∈ H := (h.omega_le _ hUmem) hu
    have hu'H : u' ∈ H := (h.omega_le _ hU'mem) hu'
    have hugH : u * u' ∈ H := H.mul_mem huH hu'H
    have hleU := Hyp78.barSub_le_zpowers_of_mem_omegaSet h hV2 hφ hUmem hwU hwJ
    have huZp : φ ⟨u, huH⟩ ∈ Subgroup.zpowers a :=
      hleU (mem_barSub.mpr ⟨⟨u, huH⟩, hu, rfl⟩)
    have hleU' := Hyp78.barSub_le_zpowers_of_mem_omegaSet h hV2 hφ hU'mem hw'U hw'J
    have hu'Zp : φ ⟨u', hu'H⟩ ∈ Subgroup.zpowers a' :=
      hleU' (mem_barSub.mpr ⟨⟨u', hu'H⟩, hu', rfl⟩)
    have hphiu : φ ⟨u, huH⟩ = 1 ∨ φ ⟨u, huH⟩ = a := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp huZp
      rcases seven_eight_core_pre_zpow_eq_one_or_self ha2 n with h1 | h1
      · left; rw [← hn]; exact h1
      · right; rw [← hn]; exact h1
    have hphiu' : φ ⟨u', hu'H⟩ = 1 ∨ φ ⟨u', hu'H⟩ = a' := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu'Zp
      rcases seven_eight_core_pre_zpow_eq_one_or_self ha'2 n with h1 | h1
      · left; rw [← hn]; exact h1
      · right; rw [← hn]; exact h1
    have hphi_mul : φ ⟨u * u', hugH⟩ = φ ⟨u, huH⟩ * φ ⟨u', hu'H⟩ := by
      rw [show (⟨u * u', hugH⟩ : ↥H) = ⟨u, huH⟩ * ⟨u', hu'H⟩ from Subtype.ext rfl, map_mul]
    have hcent := seven_eight_core_pre_zpowers_le_centralizer hφ hugH hcomm
    rcases hphiu with hu1 | hua
    · rcases hphiu' with hu'1 | hu'a
      · apply (hφ.ker_iff ⟨u * u', hugH⟩).mp
        rw [hphi_mul, hu1, hu'1, mul_one]
      · exfalso
        have hval : φ ⟨u * u', hugH⟩ = a' := by rw [hphi_mul, hu1, hu'a, one_mul]
        have hca : a' ∈ Subgroup.centralizer (Xb : Set Q) := by
          rw [← hval]; exact hcent (Subgroup.mem_zpowers _)
        exact (hne a' ha'Δ) (seven_eight_core_pre_commutator_zpowers_eq_bot_of_centralizes hca)
    · rcases hphiu' with hu'1 | hu'a
      · exfalso
        have hval : φ ⟨u * u', hugH⟩ = a := by rw [hphi_mul, hua, hu'1, mul_one]
        have hca : a ∈ Subgroup.centralizer (Xb : Set Q) := by
          rw [← hval]; exact hcent (Subgroup.mem_zpowers _)
        exact (hne a haΔ) (seven_eight_core_pre_commutator_zpowers_eq_bot_of_centralizes hca)
      · exfalso
        have hval : φ ⟨u * u', hugH⟩ = a * a' := by rw [hphi_mul, hua, hu'a]
        have hga_cent : a * a' ∈ Subgroup.centralizer (Xb : Set Q) := by
          rw [← hval]; exact hcent (Subgroup.mem_zpowers _)
        have hnotcomm : ∃ q ∈ Xb, q * a ≠ a * q := by
          by_contra h'
          push Not at h'
          apply hne a haΔ
          exact seven_eight_core_pre_commutator_zpowers_eq_bot_of_centralizes
            (Subgroup.mem_centralizer_iff.mpr fun q hq => h' q hq)
        obtain ⟨q, hqX, hqne⟩ := hnotcomm
        let m : Q := ⁅q, a⁆
        have haNorm : a ∈ Subgroup.normalizer (Xb : Set Q) := by
          have haBar : a ∈ barSub H φ L := by
            rw [hadef]
            exact mem_barSub.mpr ⟨⟨w, hwH⟩, hwL, rfl⟩
          exact hXL haBar
        have hmX : m ∈ Xb := by
          have hle := commutator_zpowers_le (Y := Xb) (d := a) haNorm
          exact hle (Subgroup.commutator_mem_commutator hqX (Subgroup.mem_zpowers a))
        have hm1 : m ≠ 1 := by
          intro h1
          exact hqne (commutatorElement_eq_one_iff_mul_comm.mp h1)
        have hmOdd : Odd (orderOf m) := by
          haveI : Fact p.Prime := ⟨hp⟩
          obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hXp) ⟨m, hmX⟩
          rw [← Subgroup.orderOf_mk m hmX, hk]
          exact (hp.odd_of_ne_two hp2).pow
        have hinv : a * m * a⁻¹ = m⁻¹ := seven_eight_core_pre_inv_commutator_self ha2
        have hc : a * a' * m = m * (a * a') :=
          (Subgroup.mem_centralizer_iff.mp hga_cent m hmX).symm
        have hcomm_aa' : a * a' = a' * a := by
          show φ ⟨w, hwH⟩ * φ ⟨w', hw'H⟩ = φ ⟨w', hw'H⟩ * φ ⟨w, hwH⟩
          rw [← map_mul, ← map_mul, show (⟨w, hwH⟩ : ↥H) * ⟨w', hw'H⟩ =
            ⟨w', hw'H⟩ * ⟨w, hwH⟩ from Subtype.ext (hUU' w hwU w' hw'U)]
        have haa' : a ≠ a' := by
          intro hab
          have h1 : φ (⟨w, hwH⟩⁻¹ * ⟨w', hw'H⟩) = 1 := by
            rw [map_mul, map_inv, ← hadef, ← ha'def, hab, inv_mul_cancel]
          have h2 : w⁻¹ * w' ∈ J := by
            have h2' : ((⟨w, hwH⟩⁻¹ * ⟨w', hw'H⟩ : ↥H) : G) ∈ J := (hφ.ker_iff _).mp h1
            simpa using h2'
          exact hxy h2
        obtain ⟨hnotodd, hnotpow⟩ :=
          orderOf_mul_not_odd_and_ne_two_pow ha2 ha'2 hcomm_aa' haa' hmOdd hm1 hinv hc
        obtain ⟨k, hkφ⟩ := hφ.surjective m
        let d : G := (k : G)⁻¹ * w * (k : G)
        have hdH : d ∈ H := H.mul_mem (H.mul_mem (H.inv_mem k.2) hwH) k.2
        have hdW : d ∈ conjSubgroup (conjSubgroup V x⁻¹) k := by
          rw [mem_conjSubgroup_iff]
          rw [show (k : G) * d * (k : G)⁻¹ = w by
            rw [show d = (k : G)⁻¹ * w * (k : G) from rfl]; group]
          exact hwU
        have hdU : conjSubgroup (conjSubgroup V x⁻¹) k ∈ omegaSet V H E :=
          conjSubgroup_mem_omegaSet h.le h.normal hUmem k.2
        have hzphi : φ ⟨d * w', H.mul_mem hdH hw'H⟩ = m⁻¹ * a * m * a' := by
          rw [show (⟨d * w', H.mul_mem hdH hw'H⟩ : ↥H) =
              ⟨d, hdH⟩ * ⟨w', hw'H⟩ from Subtype.ext rfl, map_mul]
          have hdphi : φ ⟨d, hdH⟩ = m⁻¹ * a * m := by
            rw [show (⟨d, hdH⟩ : ↥H) = k⁻¹ * ⟨w, hwH⟩ * k from Subtype.ext rfl,
              map_mul, map_mul, map_inv, hkφ, ← hadef]
          rw [hdphi, ← ha'def]
        have hdw_mem : d * w' ∈ Subgroup.closure ({d, w'} : Set G) :=
          Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
        by_cases hP : IsPGroup 2 (Subgroup.closure ({d, w'} : Set G))
        · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
          obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨d * w', hdw_mem⟩
          have horder : orderOf (d * w') = 2 ^ j :=
            (Subgroup.orderOf_mk (d * w') hdw_mem).symm.trans hj
          have hdvd : orderOf (m⁻¹ * a * m * a') ∣ 2 ^ j := by
            have h1 : orderOf (φ ⟨d * w', H.mul_mem hdH hw'H⟩) ∣
                orderOf (⟨d * w', H.mul_mem hdH hw'H⟩ : ↥H) := orderOf_map_dvd φ _
            rw [hzphi, Subgroup.orderOf_mk, horder] at h1
            exact h1
          obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
          exact hnotpow l hl
        · have hodd_dw : Odd (orderOf (d * w')) :=
            seven_three_A h.elemAbelian h.ti h.abelian hdU hU'mem hdW hw'U hP
          have hodd_e : Odd (orderOf (m⁻¹ * a * m * a')) := by
            have h1 : orderOf (φ ⟨d * w', H.mul_mem hdH hw'H⟩) ∣
                orderOf (⟨d * w', H.mul_mem hdH hw'H⟩ : ↥H) := orderOf_map_dvd φ _
            rw [hzphi, Subgroup.orderOf_mk] at h1
            exact hodd_dw.of_dvd_nat h1
          exact hnotodd hodd_e
  exact hyp76_sup_of_commute h.toHyp73 hp hp2 hUmem hU'mem hUU'
    (le_barPre hJH hφ Xb) (barPre_le H φ Xb) hAX hfaith hexpG

end CFSG.LocalAnalysis.WeakClosure81

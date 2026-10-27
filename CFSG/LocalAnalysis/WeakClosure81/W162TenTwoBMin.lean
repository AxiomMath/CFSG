module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenCore
import CFSG.LocalAnalysis.WeakClosure81.W162TenTwoBGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Hyp1510

variable {M V₀ V U S H P Q₀ : Subgroup G}

private theorem w162_min_mem_of_odd_index {X N : Subgroup G}
    (hN : (N.subgroupOf X).Normal) (hodd : Odd (N.subgroupOf X).index) {g : G} (hg : g ∈ X)
    (hk : ∃ k : ℕ, orderOf g = 2 ^ k) : g ∈ N := by
  haveI := hN
  obtain ⟨k, hk⟩ := hk
  set gX : ↥X := ⟨g, hg⟩ with hgX
  have hgo : orderOf gX = 2 ^ k := by
    rw [hgX, Subgroup.orderOf_mk]
    exact hk
  have h1 : orderOf (gX : ↥X ⧸ N.subgroupOf X) ∣ 2 ^ k :=
    hgo ▸ orderOf_map_dvd (QuotientGroup.mk' (N.subgroupOf X)) gX
  have h2 : orderOf (gX : ↥X ⧸ N.subgroupOf X) ∣ (N.subgroupOf X).index := by
    rw [Subgroup.index_eq_card]
    exact _root_.orderOf_dvd_natCard _
  have h3 : Odd (orderOf (gX : ↥X ⧸ N.subgroupOf X)) := Odd.of_dvd_nat hodd h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have hj0 : j = 0 := by
    by_contra hj0
    rw [hj] at h3
    exact (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hj0⟩)) h3
  rw [hj0, pow_zero] at hj
  have h4 : (gX : ↥X ⧸ N.subgroupOf X) = 1 := orderOf_eq_one_iff.mp hj
  have h5 : gX ∈ N.subgroupOf X := (QuotientGroup.eq_one_iff gX).mp h4
  exact h5

theorem w162_comm_mem_iHull15 (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P)
    (hQ : OddCore15 V₀ U H Q₀) {Y : Subgroup G} (hIY : iHull15 V₀ U H ≤ Y) (hYQ : Y ≤ Q₀)
    (hne : ¬ Q₀ ≤ Y) (hPY : P ≤ normalizer (Y : Set G)) :
    ∀ y ∈ Y, ∀ v ∈ V₀, ⁅y, v⁆ ∈ iHull15 V₀ U H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ_le_H : Q₀ ≤ H := hQ.le_H hP
  have hYP_le : Y ⊔ P ≤ H := sup_le (hYQ.trans hQ_le_H) hP.P_le
  have hP_le_sup : P ≤ Y ⊔ P := le_sup_right
  have hcomm : ∀ x ∈ zSub15 V₀ U (Y ⊔ P), ∀ y ∈ zSub15 V₀ U (Y ⊔ P), x * y = y * x :=
    fun x hx y hy => hP.fam.comm x ((conjClosure_mono le_rfl hYP_le) hx)
      y ((conjClosure_mono le_rfl hYP_le) hy)
  intro y hy v hv
  by_cases hV : V ≤ pCoreOf 2 (Y ⊔ P)
  ·
    have hy_sup : y ∈ (Y ⊔ P : Subgroup G) := Subgroup.mem_sup_left hy
    have hvP : v ∈ P := hP.V₀_le hv
    have hvM : v ∈ pCoreOf 2 (Y ⊔ P) := hV (h.hyp.h6.le hv)
    have hzY : ⁅y, v⁆ ∈ Y := by
      have h1 : v * y⁻¹ * v⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.1 (hPY hvP) y⁻¹).1 (Y.inv_mem hy)
      rw [commutatorElement_def]
      simpa only [mul_assoc] using Y.mul_mem hy h1
    have hzM : ⁅y, v⁆ ∈ pCoreOf 2 (Y ⊔ P) := by
      have h1 : y * v * y⁻¹ ∈ pCoreOf 2 (Y ⊔ P) :=
        (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ P) hy_sup) v).1 hvM
      rw [commutatorElement_def]
      exact (pCoreOf 2 (Y ⊔ P)).mul_mem h1 ((pCoreOf 2 (Y ⊔ P)).inv_mem hvM)
    have hzpow : ∃ k, orderOf ⁅y, v⁆ = 2 ^ k := by
      obtain ⟨k, hk⟩ :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Y ⊔ P)).exists_orderOf_eq_pow
          (⟨⁅y, v⁆, hzM⟩ : ↥(pCoreOf 2 (Y ⊔ P)))
      exact ⟨k, (Subgroup.orderOf_coe _).trans hk⟩
    exact w162_min_mem_of_odd_index (X := Q₀) (N := iHull15 V₀ U H)
      (hQ.normal_subgroupOf hP) hQ.odd (hYQ hzY) hzpow
  ·
    have hfam : Fam15 V₀ V U S (Y ⊔ P) :=
      ⟨hP.S_le.trans hP_le_sup, hV, hcomm⟩
    have h_eq : Y ⊔ P = H := hP.minimal (Y ⊔ P) hYP_le hP_le_sup hfam
    exfalso
    apply hne
    have hQ_le : Q₀ ≤ Y ⊔ P := by rw [h_eq]; exact hQ_le_H
    intro x hxQ
    have hxsup : x ∈ (Y ⊔ P : Subgroup G) := hQ_le hxQ
    have hxPY : x ∈ (P ⊔ Y : Subgroup G) := by rw [sup_comm]; exact hxsup
    have hxmul : x ∈ (↑P * ↑Y : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right P Y hPY]
      exact hxPY
    obtain ⟨u, huP, w, hwY, huw⟩ := hxmul
    have huQ : u ∈ Q₀ := by
      have h1 : u = x * w⁻¹ := by rw [← huw]; group
      rw [h1]
      exact Q₀.mul_mem hxQ (Q₀.inv_mem (hYQ hwY))
    have hupow : ∃ k, orderOf u = 2 ^ k := by
      obtain ⟨k, hk⟩ := (hP.sylow.isPGroup).exists_orderOf_eq_pow (⟨u, huP⟩ : ↥P)
      exact ⟨k, (Subgroup.orderOf_coe _).trans hk⟩
    have huI : u ∈ iHull15 V₀ U H :=
      w162_min_mem_of_odd_index (X := Q₀) (N := iHull15 V₀ U H)
        (hQ.normal_subgroupOf hP) hQ.odd huQ hupow
    rw [← huw]
    exact Y.mul_mem (hIY huI) hwY

theorem w162_exp_class (hI : NamedInputs15 G) (hW : W15Eight1 G)
    (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P)
    (hQ : OddCore15 V₀ U H Q₀) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (∀ y ∈ Q₀, y ^ p ∈ iHull15 V₀ U H) ∧
      ∀ x ∈ Q₀, ∀ y ∈ Q₀, ∀ z ∈ Q₀, ⁅⁅x, y⁆, z⁆ ∈ iHull15 V₀ U H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIH : iHull15 V₀ U H ≤ H :=
    (Hyp1510.iHull15_le_kHull15 V₀ U H).trans hP.kHull15_le
  have hQH : Q₀ ≤ H := hQ.le_H hP
  have hV0H : V₀ ≤ H := hP.V₀_le_H
  have hPH : P ≤ H := hP.P_le
  let I' : Subgroup ↥H := (iHull15 V₀ U H).subgroupOf H
  haveI hI'norm : I'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIH).2
      (Hyp1510.le_normalizer_iHull15 V₀ U H)
  let Γ := ↥H ⧸ I'
  let π : ↥H →* Γ := QuotientGroup.mk' I'
  haveI hΓfin : Finite Γ := by show Finite (↥H ⧸ I'); infer_instance
  let Q' : Subgroup ↥H := Q₀.subgroupOf H
  haveI hQ'norm : Q'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).2 hQ.normal
  let N : Subgroup Γ := Q'.map π
  haveI hNnorm : N.Normal := hQ'norm.map π (QuotientGroup.mk'_surjective I')
  let P' : Subgroup ↥H := P.subgroupOf H
  let Pbar : Subgroup Γ := P'.map π
  have ht_ex : ∃ t : G, t ∈ V₀ ∧ t ∉ iHull15 V₀ U H := by
    by_contra hcon
    apply not_V₀_le_iHull15 h hP
    intro x hx
    by_contra hxI
    exact hcon ⟨x, hx, hxI⟩
  obtain ⟨t, htV, htI⟩ := ht_ex
  have htH : t ∈ H := hV0H htV
  let tH : ↥H := ⟨t, htH⟩
  let tbar : Γ := π tH
  have hπ : ∀ x : ↥H, π x = (x : Γ) := fun x => rfl
  have hcard : Nat.card N = (iHull15 V₀ U H).relIndex Q₀ := by
    change Nat.card (Q'.map π) = (iHull15 V₀ U H).relIndex Q₀
    rw [← Subgroup.relIndex_ker Q' π, show π.ker = I' from QuotientGroup.ker_mk' I',
      Subgroup.relIndex_subgroupOf hQH]
  have hodd : Odd (Nat.card N) := hcard.symm ▸ hQ.odd
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply OddCore15.not_le_iHull15 h hP hQ
    intro q hqQ
    have hqH : q ∈ H := hQH hqQ
    have hqN : π ⟨q, hqH⟩ ∈ N :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hqQ)
    rw [hbot] at hqN
    have hq1 : π ⟨q, hqH⟩ = 1 := Subgroup.mem_bot.mp hqN
    have : (⟨q, hqH⟩ : ↥H) ∈ I' := (QuotientGroup.eq_one_iff _).1 hq1
    exact this
  have hPbar2 : IsPGroup 2 Pbar :=
    ((hP.sylow.isPGroup).comap_subtype (K := H)).map π
  have htbar2 : tbar * tbar = 1 := by
    change π tH * π tH = 1
    have ht2' : tH * tH = 1 := by
      ext
      simpa [pow_two] using h.hyp.elemAbelian₀.2 t htV
    rw [← map_mul, ht2']
    simp
  have hVbar_le : (V₀.subgroupOf H).map π ≤ Subgroup.zpowers tbar := by
    have h2 : (v1Sub15 V₀ U).relIndex V₀ = 2 := hW.relIndex_eq_two hS h
    obtain ⟨a, haV, haV1, ha⟩ :=
      (Subgroup.relIndex_eq_two_iff_exists_notMem_and' (H := v1Sub15 V₀ U)
        (K := V₀)).1 h2
    have htV1 : t ∉ v1Sub15 V₀ U := fun ht1 =>
      htI ((Hyp1510.v1Sub15_le_iHull15 V₀ U H) ht1)
    have hat : a * t ∈ v1Sub15 V₀ U := (ha t htV).resolve_right htV1
    rintro z ⟨v, hv, rfl⟩
    have hvV : (v : G) ∈ V₀ := hv
    rcases ha (v : G) hvV with hav | hv1
    · have hta : π ⟨a, hV0H haV⟩ * tbar = 1 := by
        have hmem : (⟨a, hV0H haV⟩ * tH : ↥H) ∈ I' :=
          (Hyp1510.v1Sub15_le_iHull15 V₀ U H) hat
        have h1 := (QuotientGroup.eq_one_iff (⟨a, hV0H haV⟩ * tH)).2 hmem
        simpa [hπ, tbar] using h1
      have hva : π ⟨a, hV0H haV⟩ * π v = 1 := by
        have hmem : (⟨a, hV0H haV⟩ * v : ↥H) ∈ I' :=
          (Hyp1510.v1Sub15_le_iHull15 V₀ U H) hav
        have h1 := (QuotientGroup.eq_one_iff (⟨a, hV0H haV⟩ * v)).2 hmem
        simpa [hπ] using h1
      have hveq : π v = tbar := by
        have heq : π ⟨a, hV0H haV⟩ * tbar = π ⟨a, hV0H haV⟩ * π v := by
          rw [hta, hva]
        exact (mul_left_cancel heq).symm
      rw [hveq]
      exact Subgroup.mem_zpowers tbar
    · have hveq : π v = 1 :=
        (QuotientGroup.eq_one_iff v).2 ((Hyp1510.v1Sub15_le_iHull15 V₀ U H) hv1)
      rw [hveq]
      exact Subgroup.one_mem _
  have hgen : N ≤ ⁅N, Subgroup.zpowers tbar⁆ := by
    have hD_le_H : ⁅Q₀, V₀⁆ ≤ H :=
      Subgroup.commutator_le.2 fun a ha b hb => by
        rw [commutatorElement_def]
        exact H.mul_mem (H.mul_mem (H.mul_mem (hQH ha) (hV0H hb)) (H.inv_mem (hQH ha)))
          (H.inv_mem (hV0H hb))
    have hcomm_eq : ⁅Q₀, V₀⁆.subgroupOf H = ⁅Q', V₀.subgroupOf H⁆ := by
      apply Subgroup.map_injective (f := H.subtype) H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hD_le_H]
      change ⁅Q₀, V₀⁆ = ⁅Q'.map H.subtype, (V₀.subgroupOf H).map H.subtype⁆
      rw [show Q'.map H.subtype = Q₀ ⊓ H from Subgroup.subgroupOf_map_subtype Q₀ H,
        show (V₀.subgroupOf H).map H.subtype = V₀ ⊓ H from
          Subgroup.subgroupOf_map_subtype V₀ H,
        inf_eq_left.mpr hQH, inf_eq_left.mpr hV0H]
    have h0 := OddCore15.le_commutator_sup hI hW hS h hP hQ
    have hsub : Q' ≤ ((⁅Q₀, V₀⁆ ⊔ iHull15 V₀ U H).subgroupOf H) :=
      Subgroup.subgroupOf_mono H h0
    have h1 : N ≤ ((⁅Q₀, V₀⁆ ⊔ iHull15 V₀ U H).subgroupOf H).map π :=
      Subgroup.map_mono (f := π) hsub
    rw [Subgroup.subgroupOf_sup hD_le_H hIH, Subgroup.map_sup, hcomm_eq,
      Subgroup.map_commutator, QuotientGroup.map_mk'_self I', sup_bot_eq] at h1
    exact h1.trans (Subgroup.commutator_mono le_rfl hVbar_le)
  have hmin : ∀ Y : Subgroup Γ, Y ≤ N → Y ≠ N → Pbar ≤ Subgroup.normalizer (Y : Set Γ) →
      ∀ y ∈ Y, tbar * y = y * tbar := by
    intro Y hYN hYne hPYnorm y hy
    let Y₀ : Subgroup ↥H := Y.comap π
    have hIYG : iHull15 V₀ U H ≤ Y₀.map H.subtype := by
      intro x hx
      have hxY₀ : (⟨x, hIH hx⟩ : ↥H) ∈ Y₀ := by
        rw [Subgroup.mem_comap]
        have hx1 : ((⟨x, hIH hx⟩ : ↥H) : Γ) = 1 :=
          (QuotientGroup.eq_one_iff (N := I') (⟨x, hIH hx⟩ : ↥H)).2 hx
        rw [hπ ⟨x, hIH hx⟩, hx1]
        exact Y.one_mem
      exact Subgroup.mem_map_of_mem H.subtype hxY₀
    have hker_le : π.ker ≤ Q' := by
      rw [QuotientGroup.ker_mk']
      exact Subgroup.subgroupOf_mono H hQ.iHull_le
    have hYGQ : Y₀.map H.subtype ≤ Q₀ := by
      rintro x ⟨w, hw, rfl⟩
      have hwY : π w ∈ Y := hw
      have hwN : π w ∈ N := hYN hwY
      have hwQ' : w ∈ Q' := by
        have hmem : w ∈ N.comap π := hwN
        rwa [show N = Q'.map π from rfl, Subgroup.comap_map_eq_self hker_le] at hmem
      exact hwQ'
    have hne' : ¬ Q₀ ≤ Y₀.map H.subtype := by
      intro hQYG
      apply hYne
      refine le_antisymm hYN ?_
      intro n hn
      change n ∈ Q'.map π at hn
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hn
      have hzQ : (z : G) ∈ Q₀ := hz
      have hzYG : (z : G) ∈ Y₀.map H.subtype := hQYG hzQ
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hzYG
      have hwY : π w ∈ Y := hw
      have hwz' : w = z := Subtype.ext hwz
      rwa [hwz'] at hwY
    have hPY : P ≤ Subgroup.normalizer ((Y₀.map H.subtype : Subgroup G) : Set G) := by
      have key : ∀ u ∈ P, ∀ x ∈ Y₀.map H.subtype,
          u * x * u⁻¹ ∈ Y₀.map H.subtype := by
        intro u huP x hx
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
        have huH : u ∈ H := hPH huP
        have huPbar : π ⟨u, huH⟩ ∈ Pbar :=
          Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr huP)
        have hnorm := hPYnorm huPbar
        have hwY : π w ∈ Y := hw
        have hmem : π (⟨u, huH⟩ * w * ⟨u, huH⟩⁻¹) ∈ Y := by
          have h2 := (Subgroup.mem_normalizer_iff.1 hnorm (π w)).1 hwY
          simpa only [map_mul, map_inv] using h2
        have hcomap : (⟨u, huH⟩ * w * ⟨u, huH⟩⁻¹) ∈ Y₀ := hmem
        have hmap := Subgroup.mem_map_of_mem H.subtype hcomap
        exact hmap
      intro u huP
      rw [Subgroup.mem_normalizer_iff]
      refine fun x => ⟨key u huP x, fun hx => ?_⟩
      have h1 := key u⁻¹ (P.inv_mem huP) (u * x * u⁻¹) hx
      simpa [mul_assoc] using h1
    have hcomm := w162_comm_mem_iHull15 h hP hQ hIYG hYGQ hne' hPY
    obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk'_surjective I' y
    have hy₀YG : (y₀ : G) ∈ Y₀.map H.subtype := by
      have hy₀Y₀ : y₀ ∈ Y₀ := by
        rw [Subgroup.mem_comap]
        rw [hy₀]
        exact hy
      exact Subgroup.mem_map_of_mem H.subtype hy₀Y₀
    have hcommI : ⁅(y₀ : G), t⁆ ∈ iHull15 V₀ U H := hcomm (y₀ : G) hy₀YG t htV
    have hcommbar : ((⁅y₀, tH⁆ : ↥H) : Γ) = 1 :=
      (QuotientGroup.eq_one_iff (N := I') (⁅y₀, tH⁆ : ↥H)).2 hcommI
    have h1 : ⁅y, tbar⁆ = 1 := by
      have hmap := map_commutatorElement π y₀ tH
      rw [hπ (⁅y₀, tH⁆)] at hmap
      rw [hcommbar, hy₀] at hmap
      exact hmap.symm
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  obtain ⟨p, hpprime, hp2, hpgroup, hpexp, hclass⟩ :=
    w162_exp_class_of_min (Γ := Γ) (N := N) (P := Pbar)
      hodd hPbar2 htbar2 hNne hgen hmin
  refine ⟨p, hpprime, hp2, ?_, ?_⟩
  · intro y hyQ
    have hyH : y ∈ H := hQH hyQ
    have hybar : π ⟨y, hyH⟩ ∈ N :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hyQ)
    have hpow : (π ⟨y, hyH⟩) ^ p = 1 := hpexp _ hybar
    have hpow' : π ⟨y ^ p, H.pow_mem hyH p⟩ = 1 := by
      rw [show (⟨y ^ p, H.pow_mem hyH p⟩ : ↥H) = ⟨y, hyH⟩ ^ p by ext; rfl,
        map_pow, hpow]
    have : (⟨y ^ p, H.pow_mem hyH p⟩ : ↥H) ∈ I' :=
      (QuotientGroup.eq_one_iff _).1 hpow'
    exact this
  · intro x hxQ y hyQ z hzQ
    have hxH : x ∈ H := hQH hxQ
    have hyH : y ∈ H := hQH hyQ
    have hzH : z ∈ H := hQH hzQ
    let x' : ↥H := ⟨x, hxH⟩
    let y' : ↥H := ⟨y, hyH⟩
    let z' : ↥H := ⟨z, hzH⟩
    have hxbar : π x' ∈ N :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxQ)
    have hybar : π y' ∈ N :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hyQ)
    have hzbar : π z' ∈ N :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hzQ)
    have hc : π ⁅⁅x', y'⁆, z'⁆ = 1 := by
      rw [map_commutatorElement, map_commutatorElement]
      exact hclass (π x') hxbar (π y') hybar (π z') hzbar
    have : ⁅⁅x', y'⁆, z'⁆ ∈ I' := (QuotientGroup.eq_one_iff _).1 hc
    exact this

end Hyp1510

end CFSG.LocalAnalysis.WeakClosure81

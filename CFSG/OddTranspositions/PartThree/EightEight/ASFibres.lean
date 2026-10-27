module

public import CFSG.OddTranspositions.PartThree.EightEight.ASBase
public import CFSG.OddTranspositions.PartThree.EightEight.WreathFourBlocks

import CFSG.GroupTheory.InvolutionConjParity
import CFSG.OddTranspositions.PartThree.EightEight.KOneRadical
import CFSG.OddTranspositions.PartThree.EightEight.StarOrbit
import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.Timmesfeld.Bridge.Asc72Theorem

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def barImage (D ρ S : Set G) : Set (Halpha D ρ ⧸ CFSG.solvableRadical (Halpha D ρ)) :=
  QuotientGroup.mk' (CFSG.solvableRadical (Halpha D ρ)) '' {p | (p : G) ∈ S}

omit [Finite G] in
theorem mul_mul_pow_mem_Halpha (hC : HypothesisC D) {x w y : G}
    (hx : x ∈ DalphaStar D hC.alpha) (hw : w ∈ DalphaStar D hC.alpha)
    (hy : y ∈ DalphaStar D hC.alpha) (n : ℕ) : (x * y * w) ^ n ∈ Halpha D hC.alpha := by
  have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hx
  have hyH : y ∈ Halpha D hC.alpha := Subgroup.subset_closure hy
  have hwH : w ∈ Halpha D hC.alpha := Subgroup.subset_closure hw
  exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxH hyH) hwH) n

theorem odd_ncard_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    Odd (conjOrbit (localGroup D ((x * y * w) ^ n)) x).ncard := by
  classical
  set z : G := (x * y * w) ^ n with hz
  set Δ₁ : Set G := conjOrbit (localGroup D z) x with hΔ
  have hthird := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hzx : Commute z x := by simpa [z] using hthird.2.2.1
  have hxcent : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hxK : x ∈ localGroup D z := mem_localGroup_of_mem hxcent
  have hxΔ : x ∈ Δ₁ := self_mem_conjOrbit _ x
  have hx2 : x * x = 1 := hC.setup.oddT.mul_self_eq_one ht.1
  have hmap : ∀ s ∈ Δ₁, x * s * x⁻¹ ∈ Δ₁ := fun s hs => conj_mem_conjOrbit hxK hs
  have hpar := CFSG.GroupTheory.ncard_modEq_ncard_setOf_commute (S := Δ₁)
    (Set.toFinite _) hx2 hmap
  have hthree : {s | s ∈ Δ₁ ∧ Commute x s}.ncard = 3 := by
    have h := ncard_setOf_commute_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
      (a := x) (by simpa [Δ₁, z] using hxΔ)
    have hset : {s | s ∈ Δ₁ ∧ Commute x s} = {r | r ∈ Δ₁ ∧ Commute r x} := by
      ext s
      exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
    simpa [hset, show conjOrbit (localGroup D z) x = Δ₁ from hΔ.symm] using h
  have hmod : Δ₁.ncard % 2 = 1 := by
    have h' : Δ₁.ncard % 2 = {s | s ∈ Δ₁ ∧ Commute x s}.ncard % 2 := hpar
    rw [hthree] at h'
    omega
  have : Odd Δ₁.ncard := by
    rw [Nat.odd_iff]
    exact hmod
  simpa [Δ₁, z] using this

theorem seven_le_ncard_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    7 ≤ (conjOrbit (localGroup D ((x * y * w) ^ n)) x).ncard := by
  classical
  set z : G := (x * y * w) ^ n with hz
  set Δ₁ : Set G := conjOrbit (localGroup D z) x with hΔ
  let Tx : Set G := {r | r ∈ Δ₁ ∧ Commute r x}
  let Tw : Set G := {r | r ∈ Δ₁ ∧ Commute r w}
  have hthird := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hzx : Commute z x := by simpa [z] using hthird.2.2.1
  have hzw : Commute z w := by simpa [z] using hthird.2.2.2.2.1
  have hxcent : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hwcent : w ∈ centSet D z := ⟨ht.2.2.1, hzw.symm⟩
  have hxΔ : x ∈ Δ₁ := self_mem_conjOrbit _ x
  have hwΔ : w ∈ Δ₁ := by
    simpa [Δ₁, z] using (mem_conjOrbit_of_third_kind hC.setup ht hn hord).2
  have hTx : Tx.ncard = 3 := by
    have h := ncard_setOf_commute_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
      (a := x) (by simpa [Δ₁, z] using hxΔ)
    simpa [Tx, Δ₁, z] using h
  have hTw : Tw.ncard = 3 := by
    have h := ncard_setOf_commute_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
      (a := w) (by simpa [Δ₁, z] using hwΔ)
    simpa [Tw, Δ₁, z] using h
  have hdisj : Disjoint Tx Tw := by
    rw [Set.disjoint_left]
    intro r hrx hrw
    have hrΔ : r ∈ Δ₁ := hrx.1
    have hrcent : r ∈ centSet D z := by
      have hxcent' : x ∈ centSet D z := hxcent
      exact conjOrbit_subset_centSet hC.setup.normal hxcent' (by simpa [Δ₁] using hrΔ)
    have hcomm_rx : Commute r x := hrx.2
    have hiff := commute_iff_of_commute_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn
      hord (a := r) (b := x) (by simpa [Δ₁, z] using hrΔ)
      (by simpa [Δ₁, z] using hxΔ) hcomm_rx (r := w) hwcent
    exact ht.2.2.2.2.2.1 (hiff.mp hrw.2.symm).symm
  have hcard : (Tx ∪ Tw).ncard = 6 := by
    rw [Set.ncard_union_eq hdisj, hTx, hTw]
  have h6 : 6 ≤ Δ₁.ncard := by
    rw [← hcard]
    exact Set.ncard_le_ncard (by
      rintro r (hr | hr)
      · exact hr.1
      · exact hr.1)
  have hodd : Odd Δ₁.ncard := by
    simpa [Δ₁, z] using odd_ncard_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
  rw [Nat.odd_iff] at hodd
  omega

theorem closure_conjOrbit_le_Halpha (hC : HypothesisC D)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x) ≤ Halpha D hC.alpha := by
  rw [Subgroup.closure_le]
  intro a ha
  exact Subgroup.subset_closure
    (conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord ha)

theorem subgroupOf_solvableRadical_le_center (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    ((CFSG.solvableRadical (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype).subgroupOf
        (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)) ≤
      Subgroup.center (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)) := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let K : Subgroup G := Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)
  let N : Subgroup K := (R.map H.subtype).subgroupOf K
  have hKH : K ≤ H := by
    simpa [K, H] using closure_conjOrbit_le_Halpha hC hne ht hx hw hy hn hord
  have hNnormal : N.Normal := by
    refine Subgroup.Normal.mk ?_
    intro n hn g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hn ⊢
    obtain ⟨a, ha, haeq⟩ := hn
    let gH : H := ⟨(g : G), hKH g.2⟩
    refine ⟨gH * a * gH⁻¹, (inferInstance : R.Normal).conj_mem a ha gH, ?_⟩
    calc H.subtype (gH * a * gH⁻¹) = (gH : G) * H.subtype a * (gH : G)⁻¹ := by simp
      _ = (g : G) * (n : G) * (g : G)⁻¹ := by rw [haeq]
      _ = ((g * n * g⁻¹ : K) : G) := rfl
  have hRmap : Group.IsSolvable (R.map H.subtype) := by
    have hRsolv : Group.IsSolvable R := by
      simpa [H, R] using
        CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := H)
    let : Group.IsSolvable R := hRsolv
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective R H.subtype H.subtype_injective)
  have hNsub : N.map K.subtype ≤ R.map H.subtype := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hNmap : Group.IsSolvable (N.map K.subtype) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hNsub) (Subgroup.inclusion_injective hNsub)
  have hNsolv : Group.IsSolvable N :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective N K.subtype K.subtype_injective).symm
  have hle : N ≤ CFSG.solvableRadical K :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical hNnormal hNsolv
  have hcenter : CFSG.solvableRadical K = Subgroup.center K := by
    simpa [K] using solvableRadical_closure_conjOrbit_eq_center h86 h87 hC hrad hO4 hF hne
      ht hn hord
  rwa [hcenter] at hle

theorem injOn_mk_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    Set.InjOn (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
      {p : Halpha D hC.alpha | (p : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x} := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let K : Subgroup G := Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)
  let N : Subgroup K := (R.map H.subtype).subgroupOf K
  have hNle : N ≤ Subgroup.center K := by
    simpa [H, R, K, N] using
      subgroupOf_solvableRadical_le_center h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
  have hinj := injOn_mk_center_closure_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
  intro p hp q hq hpq
  have hpK : (p : G) ∈ K := Subgroup.subset_closure (by simpa [K] using hp)
  have hqK : (q : G) ∈ K := Subgroup.subset_closure (by simpa [K] using hq)
  let pK : K := ⟨(p : G), hpK⟩
  let qK : K := ⟨(q : G), hqK⟩
  have hpqR : p⁻¹ * q ∈ R := by
    have := (QuotientGroup.eq).mp hpq
    simpa [H, R] using this
  have hmemN : pK⁻¹ * qK ∈ N := by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    exact ⟨p⁻¹ * q, hpqR, by simp [pK, qK]⟩
  have hZeq : QuotientGroup.mk' (Subgroup.center K) pK =
      QuotientGroup.mk' (Subgroup.center K) qK :=
    (QuotientGroup.eq).mpr (hNle hmemN)
  have hp' : pK ∈ CFSG.OddTranspositions.PartThree.inClosure
      (conjOrbit (localGroup D ((x * y * w) ^ n)) x) := hp
  have hq' : qK ∈ CFSG.OddTranspositions.PartThree.inClosure
      (conjOrbit (localGroup D ((x * y * w) ^ n)) x) := hq
  have hpqK : pK = qK := hinj hp' hq' hZeq
  exact Subtype.ext (by simpa [pK, qK] using congrArg Subtype.val hpqK)

theorem commute_mk_iff_of_mem_conjOrbit (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p q : Halpha D hC.alpha}
    (hp : (p : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hq : (q : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x) :
    Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q) ↔ Commute p q := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let K : Subgroup G := Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x)
  let N : Subgroup K := (R.map H.subtype).subgroupOf K
  have hNle : N ≤ Subgroup.center K := by
    simpa [H, R, K, N] using
      subgroupOf_solvableRadical_le_center h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
  have hpK : (p : G) ∈ K := Subgroup.subset_closure (by simpa [K] using hp)
  have hqK : (q : G) ∈ K := Subgroup.subset_closure (by simpa [K] using hq)
  let pK : K := ⟨(p : G), hpK⟩
  let qK : K := ⟨(q : G), hqK⟩
  have hp' : pK ∈ CFSG.OddTranspositions.PartThree.inClosure
      (conjOrbit (localGroup D ((x * y * w) ^ n)) x) := hp
  have hq' : qK ∈ CFSG.OddTranspositions.PartThree.inClosure
      (conjOrbit (localGroup D ((x * y * w) ^ n)) x) := hq
  constructor
  · intro hcomm
    have hcommR : p * q * p⁻¹ * q⁻¹ ∈ R := by
      have h1 : QuotientGroup.mk' R (p * q * p⁻¹ * q⁻¹) = 1 := by
        have hpq_eq : p * q * p⁻¹ * q⁻¹ = (p * q) * (q * p)⁻¹ := by group
        rw [hpq_eq]
        simp only [map_mul, map_inv]
        rw [hcomm.eq, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmemN : pK * qK * pK⁻¹ * qK⁻¹ ∈ N := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      exact ⟨p * q * p⁻¹ * q⁻¹, hcommR, by simp [pK, qK]⟩
    have hZ1 : QuotientGroup.mk' (Subgroup.center K) (pK * qK * pK⁻¹ * qK⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hNle hmemN)
    have hZcomm : Commute (QuotientGroup.mk' (Subgroup.center K) pK)
        (QuotientGroup.mk' (Subgroup.center K) qK) := by
      rw [commute_iff_eq]
      have h := hZ1
      simp only [map_mul, map_inv] at h
      have h2 : (QuotientGroup.mk' (Subgroup.center K) pK *
          QuotientGroup.mk' (Subgroup.center K) qK) *
          (QuotientGroup.mk' (Subgroup.center K) qK *
            QuotientGroup.mk' (Subgroup.center K) pK)⁻¹ = 1 := by
        rw [mul_inv_rev]
        simpa [mul_assoc] using h
      exact eq_of_mul_inv_eq_one h2
    have hpqK : Commute pK qK :=
      (commute_mk_center_closure_conjOrbit_iff hC ht hn hord hp' hq').mp hZcomm
    exact Subtype.ext (by simpa [pK, qK] using congrArg Subtype.val hpqK.eq)
  · intro hpq
    exact hpq.map (QuotientGroup.mk' R)

theorem commute_of_commute_mk_of_ne_mk (hC : HypothesisC D)
    {p q : Halpha D hC.alpha} (hp : p ∈ DstarH hC) (hq : q ∈ DstarH hC)
    (hne : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q)
    (hc : Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p)
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q)) :
    Commute p q := by
  by_contra hpq
  exact hne (eq_of_commute_of_odd (DstarH_isOddTransp hC) hp hq hc
    ((DstarH_isOddTransp hC).odd_of_not_commute hp hq hpq))

theorem exists_conjOrbit_pair_pow_eq (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    ∃ a' ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x,
      ∃ e ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x,
        a' ≠ x ∧ e ≠ x ∧ Commute x a' ∧ Commute x e ∧
          (x * y * w) ^ n = (x * a')⁻¹ * e := by
  classical
  let z : G := (x * y * w) ^ n
  let Δ₁ : Set G := conjOrbit (localGroup D z) x
  have hxΔ : x ∈ Δ₁ := self_mem_conjOrbit _ x
  obtain ⟨a', ha', hne', hcomm_xa', hset⟩ :=
    exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord
      (a := x) (by simpa [Δ₁, z] using hxΔ)
  have hset' : {r | r ∈ Δ₁ ∧ Commute r x} = {x, a', x * a' * z} := by
    simpa [Δ₁, z] using hset
  have he_mem : x * a' * z ∈ Δ₁ := by
    have hmem : x * a' * z ∈ ({x, a', x * a' * z} : Set G) := by simp
    rw [← hset'] at hmem
    exact hmem.1
  have hcomm_xe : Commute x (x * a' * z) := by
    have hmem : x * a' * z ∈ {r | r ∈ Δ₁ ∧ Commute r x} := by
      rw [hset']
      simp
    exact hmem.2.symm
  have he_ne : x * a' * z ≠ x := by
    simpa [z] using
      (mul_mul_pow_ne_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord hxΔ ha').1
  refine ⟨a', by simpa [Δ₁, z] using ha', x * a' * z, by simpa [Δ₁, z] using he_mem,
    by simpa [z] using hne', by simpa [z] using he_ne, by simpa [z] using hcomm_xa',
    by simpa [z] using hcomm_xe, ?_⟩
  show z = (x * a')⁻¹ * (x * a' * z)
  group

theorem commute_pow_of_mk_eq_of_commute (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p : Halpha D hC.alpha} (hp : p ∈ DstarH hC)
    (heq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨x, Subgroup.subset_closure hx⟩)
    (hcomm : Commute p ⟨x, Subgroup.subset_closure hx⟩) :
    Commute (p : G) ((x * y * w) ^ n) := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let xH : H := ⟨x, Subgroup.subset_closure hx⟩
  obtain ⟨a', ha', e, he_mem, hne_a', hne_e, hcomm_xa', hcomm_xe, hzeq⟩ :=
    exists_conjOrbit_pair_pow_eq h86 h87 hC hrad hO4 hF hne ht hn hord
  have hΔD : conjOrbit (localGroup D ((x * y * w) ^ n)) x ⊆ DalphaStar D hC.alpha :=
    conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord
  let aH : H := ⟨a', Subgroup.subset_closure (hΔD ha')⟩
  let eH : H := ⟨e, Subgroup.subset_closure (hΔD he_mem)⟩
  have ha'D : aH ∈ DstarH hC := hΔD ha'
  have heD : eH ∈ DstarH hC := hΔD he_mem
  have hinj := injOn_mk_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
  have hxa_ne : QuotientGroup.mk' R aH ≠ QuotientGroup.mk' R xH := by
    intro h
    exact hne_a' (congrArg Subtype.val
      (hinj (x₁ := aH) (x₂ := xH) ha' (self_mem_conjOrbit _ x) h))
  have hex_ne : QuotientGroup.mk' R eH ≠ QuotientGroup.mk' R xH := by
    intro h
    exact hne_e (congrArg Subtype.val
      (hinj (x₁ := eH) (x₂ := xH) he_mem (self_mem_conjOrbit _ x) h))
  have hxH_aH : Commute xH aH := Subtype.ext hcomm_xa'.eq
  have hxH_eH : Commute xH eH := Subtype.ext hcomm_xe.eq
  have hpa : Commute p aH :=
    commute_of_commute_mk_of_ne_mk hC hp ha'D (by rw [heq]; exact hxa_ne.symm)
      (by rw [heq]; exact hxH_aH.map (QuotientGroup.mk' R))
  have hpe : Commute p eH :=
    commute_of_commute_mk_of_ne_mk hC hp heD (by rw [heq]; exact hex_ne.symm)
      (by rw [heq]; exact hxH_eH.map (QuotientGroup.mk' R))
  have hp_x : Commute (p : G) x := hcomm.map H.subtype
  have hp_a : Commute (p : G) a' := hpa.map H.subtype
  have hp_e : Commute (p : G) e := hpe.map H.subtype
  rw [hzeq]
  exact ((hp_x.mul_right hp_a).inv_right).mul_right hp_e

theorem eq_of_mk_eq_of_commute (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p : Halpha D hC.alpha} (hp : p ∈ DstarH hC)
    (hpne : p ≠ ⟨x, Subgroup.subset_closure hx⟩)
    (heq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
        ⟨x, Subgroup.subset_closure hx⟩)
    (hcomm : Commute p ⟨x, Subgroup.subset_closure hx⟩) : False := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let z : G := (x * y * w) ^ n
  let Δ₁ : Set G := conjOrbit (localGroup D z) x
  let xH : H := ⟨x, Subgroup.subset_closure hx⟩
  have hxΔ : x ∈ Δ₁ := self_mem_conjOrbit _ x
  have hΔD : Δ₁ ⊆ DalphaStar D hC.alpha := by
    simpa [Δ₁, z] using conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord
  have hp_z : Commute (p : G) z :=
    commute_pow_of_mk_eq_of_commute h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord hp heq hcomm
  have hpD : (p : G) ∈ D :=
    DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hp)
  have hpcent : (p : G) ∈ centSet D z := ⟨hpD, hp_z⟩
  have hwΔ : w ∈ Δ₁ := (mem_conjOrbit_of_third_kind hC.setup ht hn hord).2
  have hwH : w ∈ H := Subgroup.subset_closure (hΔD hwΔ)
  have hnc_xw : ¬ Commute (QuotientGroup.mk' R xH) (QuotientGroup.mk' R ⟨w, hwH⟩) := by
    intro hc
    have hcxw : Commute x w :=
      ((commute_mk_iff_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
        hxΔ hwΔ).mp hc).map H.subtype
    exact ht.2.2.2.2.2.1 hcxw
  have hp_mem : (p : G) ∈ Δ₁ := by
    by_contra hpΔ
    have hpLeft : (p : G) ∈ {d | d ∈ centSet D z ∧ d ∉ Δ₁} := ⟨hpcent, hpΔ⟩
    have hset0 := setOf_centSet_notMem_eq (D := D) hC.setup ht hn hord
    rw [show {d | d ∈ centSet D z ∧ d ∉ Δ₁} =
        {d | d ∈ D ∧ ∀ a ∈ Δ₁, Commute d a} by simpa [z, Δ₁] using hset0] at hpLeft
    have hpw : Commute (p : G) w := hpLeft.2 w hwΔ
    have hpwH : Commute p ⟨w, hwH⟩ := Subtype.ext hpw.eq
    have hc : Commute (QuotientGroup.mk' R p) (QuotientGroup.mk' R ⟨w, hwH⟩) :=
      hpwH.map (QuotientGroup.mk' R)
    rw [heq] at hc
    exact hnc_xw hc
  exact hpne (injOn_mk_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
    hp_mem hxΔ heq)

theorem not_commute_of_mk_eq (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p q : Halpha D hC.alpha} (hp : p ∈ DstarH hC)
    (hq : q ∈ DstarH hC) (hpq : p ≠ q)
    (heq : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) q) :
    ¬ Commute p q := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let xH : H := ⟨x, Subgroup.subset_closure hx⟩
  have hxH_mem : xH ∈ DstarH hC := hx
  intro hcomm
  obtain ⟨h, hh⟩ := DstarH_transitive hC hp hxH_mem
  have hq_mem : h * q * h⁻¹ ∈ DstarH hC := DstarH_conj_mem hC hq
  have hq_ne : h * q * h⁻¹ ≠ xH := by
    intro hqeq
    apply hpq
    calc p = h⁻¹ * (h * p * h⁻¹) * h := by group
      _ = h⁻¹ * xH * h := by rw [hh]
      _ = h⁻¹ * (h * q * h⁻¹) * h := by rw [hqeq]
      _ = q := by group
  have heq' : QuotientGroup.mk' R (h * q * h⁻¹) = QuotientGroup.mk' R xH := by
    calc QuotientGroup.mk' R (h * q * h⁻¹)
        = QuotientGroup.mk' R h * QuotientGroup.mk' R q *
            (QuotientGroup.mk' R h)⁻¹ := by simp
      _ = QuotientGroup.mk' R h * QuotientGroup.mk' R p *
            (QuotientGroup.mk' R h)⁻¹ := by rw [← heq]
      _ = QuotientGroup.mk' R (h * p * h⁻¹) := by simp
      _ = QuotientGroup.mk' R xH := by rw [hh]
  have hcomm' : Commute (h * q * h⁻¹) xH := by
    have hc := hcomm.conj h
    rw [hh] at hc
    exact hc.symm
  exact eq_of_mk_eq_of_commute h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
    hq_mem hq_ne heq' hcomm'

theorem fibresAnticlique_of_isStarTriangle (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsStarTriangle hC x w y) : FibresAnticlique D hC.alpha := by
  obtain ⟨htri, ⟨n, hn, -, hord⟩, hx, hw, hy, -⟩ := ht
  intro a b ha hb hab heq
  exact not_commute_of_mk_eq h86 h87 hC hrad hO4 hF hne htri hx hw hy hn hord ha hb hab heq

theorem mk_ne_of_forall_commute_barImage (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p b : Halpha D hC.alpha}
    (hb : (b : G) ∈ conjOrbit (localGroup D ((x * y * w) ^ n)) x)
    (hcomm : ∀ a ∈ barImage D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x),
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p) a) :
    QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ≠
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let π : H →* H ⧸ R := QuotientGroup.mk' R
  let Δ₁ : Set G := conjOrbit (localGroup D ((x * y * w) ^ n)) x
  have hΔD : Δ₁ ⊆ DalphaStar D hC.alpha := by
    simpa [Δ₁] using conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord
  have hΔH : Δ₁ ⊆ H := fun a ha => Subgroup.subset_closure (hΔD ha)
  intro heq
  have hcomm_all : ∀ a ∈ Δ₁, Commute (b : G) a := by
    intro a ha
    let aH : H := ⟨a, hΔH ha⟩
    have haBar : π aH ∈ barImage D hC.alpha Δ₁ := ⟨aH, ha, rfl⟩
    have hc : Commute (π p) (π aH) := hcomm (π aH) haBar
    rw [heq] at hc
    exact ((commute_mk_iff_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hx hw hy hn
      hord (p := b) (q := aH) hb ha).mp hc).map H.subtype
  have hseteq : {r | r ∈ Δ₁ ∧ Commute r (b : G)} = Δ₁ := by
    ext r
    constructor
    · rintro ⟨hr, -⟩
      exact hr
    · intro hr
      exact ⟨hr, (hcomm_all r hr).symm⟩
  have h3 : {r | r ∈ Δ₁ ∧ Commute r (b : G)}.ncard = 3 := by
    simpa [Δ₁] using ncard_setOf_commute_mem_conjOrbit h86 h87 hC hrad hO4 hF hne
      ht hn hord (a := (b : G)) hb
  have h7 : 7 ≤ Δ₁.ncard := by
    simpa [Δ₁] using seven_le_ncard_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
  rw [← hseteq, h3] at h7
  omega

theorem mem_starSigma_of_forall_commute_barImage (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p : Halpha D hC.alpha}
    (hp : (p : G) ∈ DalphaStar D hC.alpha)
    (hcomm : ∀ a ∈ barImage D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x),
      Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p) a) :
    (p : G) ∈ starSigma D x w y n := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let π : H →* H ⧸ R := QuotientGroup.mk' R
  let Δ₁ : Set G := conjOrbit (localGroup D ((x * y * w) ^ n)) x
  have hΔD : Δ₁ ⊆ DalphaStar D hC.alpha := by
    simpa [Δ₁] using conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord
  have hcommG : ∀ a ∈ Δ₁, Commute (p : G) a := by
    intro a ha
    let aH : H := ⟨a, Subgroup.subset_closure (hΔD ha)⟩
    have hne_mk : π p ≠ π aH :=
      mk_ne_of_forall_commute_barImage h86 h87 hC hrad hO4 hF hne ht hx hw hy hn hord
        (b := aH) ha hcomm
    have hc : Commute (π p) (π aH) := hcomm (π aH) ⟨aH, ha, rfl⟩
    exact (commute_of_commute_mk_of_ne_mk hC hp (hΔD ha) hne_mk hc).map H.subtype
  have hset := setOf_centSet_notMem_eq (D := D) hC.setup ht hn hord
  have hpRight : (p : G) ∈ {d | d ∈ D ∧ ∀ a ∈ Δ₁, Commute d a} :=
    ⟨DalphaStar_subset hC.isBlock_alpha hp, hcommG⟩
  rwa [show {d | d ∈ D ∧ ∀ a ∈ Δ₁, Commute d a} =
      {d | d ∈ centSet D ((x * y * w) ^ n) ∧ d ∉ Δ₁} by
    simpa [Δ₁] using hset.symm] at hpRight

theorem mem_starN_iff_commute_mk (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) (hx : x ∈ DalphaStar D hC.alpha)
    (hw : w ∈ DalphaStar D hC.alpha) (hy : y ∈ DalphaStar D hC.alpha) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) {p : Halpha D hC.alpha}
    (hp : (p : G) ∈ DalphaStar D hC.alpha) :
    (p : G) ∈ starN D hC.alpha (starSigma D x w y n) ↔
      ∀ a ∈ barImage D hC.alpha (conjOrbit (localGroup D ((x * y * w) ^ n)) x),
        Commute (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p) a := by
  classical
  let H := Halpha D hC.alpha
  let R : Subgroup H := CFSG.solvableRadical H
  let Δ₁ : Set G := conjOrbit (localGroup D ((x * y * w) ^ n)) x
  have hΔD : Δ₁ ⊆ DalphaStar D hC.alpha := by
    simpa [Δ₁] using conjOrbit_subset_DalphaStar hC hne ht hx hw hy hn hord
  constructor
  · intro hpN
    have hpD : (p : G) ∈ {d | d ∈ D ∧ ∀ a ∈ Δ₁, Commute d a} := by
      have hset := setOf_centSet_notMem_eq (D := D) hC.setup ht hn hord
      rw [show {d | d ∈ D ∧ ∀ a ∈ Δ₁, Commute d a} =
          {d | d ∈ centSet D ((x * y * w) ^ n) ∧ d ∉ Δ₁} by
        simpa [Δ₁] using hset.symm]
      exact hpN.1
    intro a ha
    obtain ⟨q, hq, rfl⟩ := ha
    have hpq : Commute p q := Subtype.ext (hpD.2 (q : G) hq).eq
    exact hpq.map (QuotientGroup.mk' R)
  · intro hcomm
    exact ⟨mem_starSigma_of_forall_commute_barImage h86 h87 hC hrad hO4 hF hne ht hx hw hy
      hn hord hp hcomm, hp⟩

end CFSG.OddTranspositions.PartThree.EightEight

end

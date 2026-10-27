module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.OrderOfElement

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 2, Proposition (2.4)

This file proves Peterfalvi (2.4).  It uses only the local PF section 2
hypothesis package and general subgroup/Hall infrastructure.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section2

universe u

private theorem mem_elementCentralizer_commute {G : Type u} [Group G] {a c : G}
    (hc : c ∈ elementCentralizer a) : a * c = c * a := by
  unfold elementCentralizer at hc
  rw [Subgroup.mem_centralizer_iff] at hc
  exact hc a (by simp)

private theorem centralizerIn_le_elementCentralizer {G : Type u} [Group G]
    (L : Subgroup G) (a : G) :
    centralizerIn L a ≤ elementCentralizer a := by
  intro x hx
  exact (Subgroup.mem_inf.mp hx).2

private theorem mem_centralizerIn_self {G : Type u} [Group G]
    {L : Subgroup G} {a : G} (haL : a ∈ L) :
    a ∈ centralizerIn L a := by
  refine Subgroup.mem_inf.mpr ⟨haL, ?_⟩
  unfold elementCentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  simp

private theorem conjugateSubgroup_eq_map {G : Type u} [Group G]
    (x : G) (K : Subgroup G) :
    conjugateSubgroup x K = K.map (MulAut.conj x).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact Subgroup.mem_map.mpr ⟨k, hk, by simp [conjBy, MulAut.conj_apply]⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, by simp [conjBy, MulAut.conj_apply]⟩

private theorem natCard_conjugateSubgroup {G : Type u} [Group G]
    (x : G) (K : Subgroup G) :
    Nat.card (conjugateSubgroup x K) = Nat.card K := by
  rw [conjugateSubgroup_eq_map]
  simpa using
    (Subgroup.card_map_of_injective (K := K) (f := (MulAut.conj x).toMonoidHom)
      (MulAut.conj x).injective)

private theorem natCard_subgroupOf {G : Type u} [Group G]
    {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  simpa using
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := H) (K := K) hHK).toEquiv


private theorem internalSemidirectProduct_index_left_eq_card_right
    {G : Type u} [Group G] {C H K : Subgroup G}
    (h : IsInternalSemidirectProduct C H K) :
    (H.subgroupOf C).index = Nat.card K := by
  have hcomp := internalSemidirectProduct_isComplement (C := C) (H := H) (K := K) h
  calc
    (H.subgroupOf C).index = Nat.card (K.subgroupOf C) := by
      simpa using hcomp.symm.index_eq_card
    _ = Nat.card K := natCard_subgroupOf h.right_le


private theorem Nat.Coprime.mul_of_pairwise
    {a b c d : ℕ} (hac : Nat.Coprime a c) (had : Nat.Coprime a d)
    (hbc : Nat.Coprime b c) (hbd : Nat.Coprime b d) :
    Nat.Coprime (a * b) (c * d) :=
  Nat.Coprime.mul_left (Nat.Coprime.mul_right hac had)
    (Nat.Coprime.mul_right hbc hbd)


private theorem pow_natCard_subgroup_eq_one {G : Type u} [Group G]
    (K : Subgroup G) {x : G} (hx : x ∈ K) :
    x ^ Nat.card K = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard K hx)

private def dadePiCompl {G : Type u} [Group G] (A : Set G) (L : Subgroup G) :
    Set Nat.Primes :=
  {p | ∀ ⦃a : G⦄, a ∈ A → ¬ p.val ∣ Nat.card (centralizerIn L a)}

private theorem conjBy_mem_of_mem_A_of_mem_L {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a x : G} (ha : a ∈ A) (hx : x ∈ L) :
    conjBy x a ∈ A := by
  have hnorm : normalizesSet A x := by
    simpa [setNormalizer] using h.L_le_normalizer hx
  exact (hnorm a).2 ha

private theorem conjugateSubgroup_le_elementCentralizer_conj {G : Type u} [Group G]
    {a x : G} {K : Subgroup G} (hK : K ≤ elementCentralizer a) :
    conjugateSubgroup x K ≤ elementCentralizer (conjBy x a) := by
  intro y hy
  rcases hy with ⟨k, hk, rfl⟩
  unfold elementCentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  have hcomm := mem_elementCentralizer_commute (hK hk)
  calc
    conjBy x a * conjBy x k =
        x * (a * k) * x⁻¹ := by simp [conjBy, mul_assoc]
    _ = x * (k * a) * x⁻¹ := by rw [hcomm]
    _ = conjBy x k * conjBy x a := by simp [conjBy, mul_assoc]

private theorem conjugateSubgroup_elementCentralizer_eq {G : Type u} [Group G]
    (x a : G) :
    conjugateSubgroup x (elementCentralizer a) = elementCentralizer (conjBy x a) := by
  apply le_antisymm
  · exact conjugateSubgroup_le_elementCentralizer_conj (le_refl _)
  · intro y hy
    refine ⟨conjBy x⁻¹ y, ?_, ?_⟩
    · unfold elementCentralizer at hy ⊢
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      have hcomm : conjBy x a * y = y * conjBy x a := hy (conjBy x a) (by simp)
      simpa [conjBy, mul_assoc] using congrArg (fun t => x⁻¹ * t * x) hcomm
    · simp [conjBy, mul_assoc]

private theorem conjugateSubgroup_centralizerIn_eq {G : Type u} [Group G]
    {L : Subgroup G} {x a : G} (hx : x ∈ L) :
    conjugateSubgroup x (centralizerIn L a) = centralizerIn L (conjBy x a) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact L.mul_mem (L.mul_mem hx (Subgroup.mem_inf.mp hk).1) (L.inv_mem hx)
    · exact conjugateSubgroup_le_elementCentralizer_conj
        (centralizerIn_le_elementCentralizer L a) ⟨k, hk, rfl⟩
  · intro y hy
    refine ⟨conjBy x⁻¹ y, ?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact L.mul_mem (L.mul_mem (L.inv_mem hx) (Subgroup.mem_inf.mp hy).1)
          (L.inv_mem (L.inv_mem hx))
      · have hcent : conjBy x⁻¹ y ∈ elementCentralizer a := by
          have hcomm :=
            mem_elementCentralizer_commute (Subgroup.mem_inf.mp hy).2
          unfold elementCentralizer
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          subst z
          simpa [conjBy, mul_assoc] using congrArg (fun t => x⁻¹ * t * x) hcomm
        exact hcent
    · simp [conjBy, mul_assoc]

private theorem internalSemidirectProduct_left_normal {G : Type u} [Group G]
    {C H K : Subgroup G} (h : IsInternalSemidirectProduct C H K) :
    (H.subgroupOf C).Normal := by
  refine ⟨?_⟩
  intro y hyH x
  rcases h.mul_surjective (x : G) x.2 with ⟨h0, hh0, k0, hk0, hx⟩
  change ((x : G) * (y : G) * (x : G)⁻¹) ∈ H
  rw [hx]
  have hky : conjBy k0 (y : G) ∈ H :=
    h.right_normalizes_left k0 hk0 (y : G) hyH
  have hcalc :
      h0 * k0 * (y : G) * (h0 * k0)⁻¹ =
        h0 * conjBy k0 (y : G) * h0⁻¹ := by
    simp [conjBy, mul_assoc]
  rw [hcalc]
  exact H.mul_mem (H.mul_mem hh0 hky) (H.inv_mem hh0)

private theorem internalSemidirectProduct_conjugate {G : Type u} [Group G]
    {C H K : Subgroup G} (h : IsInternalSemidirectProduct C H K) (x : G) :
    IsInternalSemidirectProduct
      (conjugateSubgroup x C) (conjugateSubgroup x H) (conjugateSubgroup x K) where
  left_le := by
    rintro y ⟨h0, hh0, rfl⟩
    exact ⟨h0, h.left_le hh0, rfl⟩
  right_le := by
    rintro y ⟨k0, hk0, rfl⟩
    exact ⟨k0, h.right_le hk0, rfl⟩
  right_normalizes_left := by
    rintro _ ⟨k0, hk0, rfl⟩ _ ⟨h0, hh0, rfl⟩
    refine ⟨conjBy k0 h0, h.right_normalizes_left k0 hk0 h0 hh0, ?_⟩
    simp [conjBy, mul_assoc]
  inf_eq_bot := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases (Subgroup.mem_inf.mp hy).1 with ⟨h0, hh0, hyh⟩
    rcases (Subgroup.mem_inf.mp hy).2 with ⟨k0, hk0, hyk⟩
    have hconj_eq : conjBy x h0 = conjBy x k0 := hyh.symm.trans hyk
    have hhk : h0 = k0 := by
      simpa [conjBy, MulAut.conj_apply] using (MulAut.conj x).injective hconj_eq
    subst k0
    have hbot : h0 ∈ (⊥ : Subgroup G) := by
      have hinf : h0 ∈ H ⊓ K := Subgroup.mem_inf.mpr ⟨hh0, hk0⟩
      simpa [h.inf_eq_bot] using hinf
    rw [hyh]
    simpa [conjBy] using hbot
  mul_surjective := by
    rintro y ⟨c, hc, rfl⟩
    rcases h.mul_surjective c hc with ⟨h0, hh0, k0, hk0, hc_eq⟩
    refine ⟨conjBy x h0, ⟨h0, hh0, rfl⟩,
      conjBy x k0, ⟨k0, hk0, rfl⟩, ?_⟩
    rw [hc_eq]
    simp [conjBy, mul_assoc]

private theorem internalSemidirectProduct_conjugate_to_centralizer {G : Type u} [Group G]
    {L H : Subgroup G} {a x : G}
    (h : IsInternalSemidirectProduct (elementCentralizer a) H (centralizerIn L a))
    (hx : x ∈ L) :
    IsInternalSemidirectProduct
      (elementCentralizer (conjBy x a)) (conjugateSubgroup x H)
      (centralizerIn L (conjBy x a)) := by
  have hconj := internalSemidirectProduct_conjugate h x
  simpa [conjugateSubgroup_elementCentralizer_eq x a,
    conjugateSubgroup_centralizerIn_eq (L := L) (x := x) (a := a) hx] using hconj

private theorem subgroupOf_eq_of_eq {G : Type u} [Group G]
    {C H K : Subgroup G} (hH : H ≤ C) (hK : K ≤ C)
    (hEq : H.subgroupOf C = K.subgroupOf C) :
    H = K := by
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hH hx⟩ : C) ∈ H.subgroupOf C := hx
    rw [hEq] at hx'
    exact hx'
  · intro hx
    have hx' : (⟨x, hK hx⟩ : C) ∈ K.subgroupOf C := hx
    rw [← hEq] at hx'
    exact hx'

private theorem hFactor_isHall {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a : G} (ha : a ∈ A) :
    IsHallSubgroup (dadePiCompl A L) ((H a).subgroupOf (elementCentralizer a)) := by
  let C := elementCentralizer a
  have hprod := h.centralizer_eq_product ha
  have hcard_sub :
      Nat.card ((H a).subgroupOf C) = Nat.card (H a) :=
    natCard_subgroupOf hprod.left_le
  refine isHallSubgroup_of (G := C) (π := dadePiCompl A L)
    (H := (H a).subgroupOf C) ?_ ?_
  · intro p hp_dvd b hb
    have hp_dvd_H : p.val ∣ Nat.card (H a) := by
      rw [hcard_sub] at hp_dvd
      simpa using hp_dvd
    exact (p.property.coprime_iff_not_dvd).1
      ((h.coprime_orders ha hb).coprime_dvd_left hp_dvd_H)
  · intro p hp_mem hp_dvd_index
    have hindex : ((H a).subgroupOf C).index = Nat.card (centralizerIn L a) := by
      simpa [C] using
        (internalSemidirectProduct_index_left_eq_card_right
          (C := elementCentralizer a) (H := H a) (K := centralizerIn L a) hprod)
    exact hp_mem ha (by simpa [hindex] using hp_dvd_index)

private theorem conjugateH_isHall {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a x : G} (ha : a ∈ A) (hx : x ∈ L) :
    IsHallSubgroup (dadePiCompl A L)
      ((conjugateSubgroup x (H a)).subgroupOf (elementCentralizer (conjBy x a))) := by
  let a' := conjBy x a
  let C' := elementCentralizer a'
  have ha' : a' ∈ A := conjBy_mem_of_mem_A_of_mem_L h ha hx
  have hprod :=
    internalSemidirectProduct_conjugate_to_centralizer
      (L := L) (a := a) (x := x) (H := H a)
      (h.centralizer_eq_product ha) hx
  refine isHallSubgroup_of (G := C') (π := dadePiCompl A L)
    (H := (conjugateSubgroup x (H a)).subgroupOf C') ?_ ?_
  · intro p hp_dvd b hb
    have hcard_sub :
        Nat.card ((conjugateSubgroup x (H a)).subgroupOf C') =
          Nat.card (conjugateSubgroup x (H a)) :=
      natCard_subgroupOf hprod.left_le
    have hp_dvd_H : p.val ∣ Nat.card (H a) := by
      rw [hcard_sub] at hp_dvd
      rw [natCard_conjugateSubgroup] at hp_dvd
      simpa using hp_dvd
    exact (p.property.coprime_iff_not_dvd).1
      ((h.coprime_orders ha hb).coprime_dvd_left hp_dvd_H)
  · intro p hp_mem hp_dvd_index
    have hindex :
        ((conjugateSubgroup x (H a)).subgroupOf C').index =
          Nat.card (centralizerIn L a') := by
      simpa [C', a'] using
        (internalSemidirectProduct_index_left_eq_card_right
          (C := elementCentralizer a') (H := conjugateSubgroup x (H a))
          (K := centralizerIn L a') hprod)
    exact hp_mem ha' (by simpa [hindex] using hp_dvd_index)

private theorem hFactor_conjugate_eq {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a x : G} (ha : a ∈ A) (hx : x ∈ L) :
    H (conjBy x a) = conjugateSubgroup x (H a) := by
  let a' := conjBy x a
  let C' := elementCentralizer a'
  have ha' : a' ∈ A := conjBy_mem_of_mem_A_of_mem_L h ha hx
  have hprod' := h.centralizer_eq_product ha'
  have hHle : H a' ≤ C' := by
    simpa [C', a'] using hprod'.left_le
  have hKle : conjugateSubgroup x (H a) ≤ C' := by
    have hprod :=
      internalSemidirectProduct_conjugate_to_centralizer
        (L := L) (a := a) (x := x) (H := H a)
        (h.centralizer_eq_product ha) hx
    simpa [C', a'] using hprod.left_le
  haveI : ((H a').subgroupOf C').Normal := by
    simpa [C', a'] using internalSemidirectProduct_left_normal hprod'
  have hHallH : IsHallSubgroup (dadePiCompl A L) ((H a').subgroupOf C') := by
    simpa [C', a'] using hFactor_isHall h ha'
  have hHallK :
      IsHallSubgroup (dadePiCompl A L) ((conjugateSubgroup x (H a)).subgroupOf C') := by
    simpa [C', a'] using conjugateH_isHall h ha hx
  have hsub :
      ((conjugateSubgroup x (H a)).subgroupOf C') = (H a').subgroupOf C' :=
    IsHallSubgroup.eq_of_normal hHallH hHallK
  exact subgroupOf_eq_of_eq hHle hKle hsub.symm

private theorem conjBy_pow {G : Type u} [Group G] (x y : G) (n : ℕ) :
    conjBy x (y ^ n) = conjBy x y ^ n := by
  simp [conjBy]

private theorem conjugateIn_symm {G : Type u} [Group G] {a b : G}
    (h : conjugateIn a b) :
    conjugateIn b a := by
  rcases h with ⟨x, rfl⟩
  refine ⟨x⁻¹, ?_⟩
  simp [conjBy, mul_assoc]

private theorem conjugateIn_trans {G : Type u} [Group G] {a b c : G}
    (hab : conjugateIn a b) (hbc : conjugateIn b c) :
    conjugateIn a c := by
  rcases hab with ⟨x, rfl⟩
  rcases hbc with ⟨y, rfl⟩
  refine ⟨y * x, ?_⟩
  simp [conjBy, mul_assoc]

private theorem conjugate_base_of_coset_conjugate {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a b u v : G}
    (ha : a ∈ A) (hb : b ∈ A) (hu : u ∈ H a) (hv : v ∈ H b)
    (hconj : conjugateIn (a * u) (b * v)) :
    conjugateIn a b := by
  let N := Nat.card (H a) * Nat.card (H b)
  have huN : u ^ N = 1 := by
    dsimp [N]
    rw [pow_mul, pow_natCard_subgroup_eq_one (H a) hu]
    simp
  have hvN : v ^ N = 1 := by
    dsimp [N]
    rw [Nat.mul_comm, pow_mul, pow_natCard_subgroup_eq_one (H b) hv]
    simp
  have haCL : a ∈ centralizerIn L a :=
    mem_centralizerIn_self (h.subset_L a ha)
  have hbCL : b ∈ centralizerIn L b :=
    mem_centralizerIn_self (h.subset_L b hb)
  have horda : orderOf a ∣ Nat.card (centralizerIn L a) :=
    Subgroup.orderOf_dvd_natCard (centralizerIn L a) haCL
  have hordb : orderOf b ∣ Nat.card (centralizerIn L b) :=
    Subgroup.orderOf_dvd_natCard (centralizerIn L b) hbCL
  have hHa_oa : Nat.Coprime (Nat.card (H a)) (orderOf a) :=
    (h.coprime_orders ha ha).of_dvd_right horda
  have hHa_ob : Nat.Coprime (Nat.card (H a)) (orderOf b) :=
    (h.coprime_orders ha hb).of_dvd_right hordb
  have hHb_oa : Nat.Coprime (Nat.card (H b)) (orderOf a) :=
    (h.coprime_orders hb ha).of_dvd_right horda
  have hHb_ob : Nat.Coprime (Nat.card (H b)) (orderOf b) :=
    (h.coprime_orders hb hb).of_dvd_right hordb
  have hprod :
      Nat.Coprime (Nat.card (H a) * Nat.card (H b)) (orderOf a * orderOf b) :=
    Nat.Coprime.mul_of_pairwise hHa_oa hHa_ob hHb_oa hHb_ob
  have hN_pair : Nat.Coprime N (orderOf (a, b)) := by
    dsimp [N]
    rw [Prod.orderOf_mk]
    exact hprod.of_dvd_right
      (Nat.lcm_dvd (dvd_mul_right _ _) (dvd_mul_left _ _))
  rcases exists_pow_eq_self_of_coprime (x := (a, b)) hN_pair with ⟨m, hm⟩
  have hpair : ((a, b) : G × G) ^ (N * m) = (a, b) := by
    simpa [pow_mul] using hm
  have haNm : a ^ (N * m) = a := by
    simpa using congrArg Prod.fst hpair
  have hbNm : b ^ (N * m) = b := by
    simpa using congrArg Prod.snd hpair
  have huNm : u ^ (N * m) = 1 := by
    rw [pow_mul, huN]
    simp
  have hvNm : v ^ (N * m) = 1 := by
    rw [pow_mul, hvN]
    simp
  have hau_comm : Commute a u := by
    exact mem_elementCentralizer_commute ((h.centralizer_eq_product ha).left_le hu)
  have hbv_comm : Commute b v := by
    exact mem_elementCentralizer_commute ((h.centralizer_eq_product hb).left_le hv)
  have hau_pow : (a * u) ^ (N * m) = a := by
    calc
      (a * u) ^ (N * m) = a ^ (N * m) * u ^ (N * m) :=
        hau_comm.mul_pow (N * m)
      _ = a := by simp [haNm, huNm]
  have hbv_pow : (b * v) ^ (N * m) = b := by
    calc
      (b * v) ^ (N * m) = b ^ (N * m) * v ^ (N * m) :=
        hbv_comm.mul_pow (N * m)
      _ = b := by simp [hbNm, hvNm]
  rcases hconj with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  have hxpow : conjBy x ((a * u) ^ (N * m)) = (b * v) ^ (N * m) := by
    calc
      conjBy x ((a * u) ^ (N * m)) = conjBy x (a * u) ^ (N * m) :=
        conjBy_pow x (a * u) (N * m)
      _ = (b * v) ^ (N * m) := by rw [hx]
  simpa [hau_pow, hbv_pow] using hxpow

private theorem conjBy_eq_self_of_mem_elementCentralizer {G : Type u} [Group G]
    {a g : G} (hg : g ∈ elementCentralizer a) :
    conjBy g a = a := by
  have hcomm := mem_elementCentralizer_commute hg
  calc
    conjBy g a = g * a * g⁻¹ := rfl
    _ = a * g * g⁻¹ := by rw [hcomm.symm]
    _ = a := by simp [mul_assoc]

private theorem mem_elementCentralizer_of_conjBy_eq_self {G : Type u} [Group G]
    {a g : G} (hga : conjBy g a = a) :
    g ∈ elementCentralizer a := by
  unfold elementCentralizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  calc
    a * g = conjBy g a * g := by rw [hga]
    _ = g * a := by simp [conjBy, mul_assoc]

private theorem conjBy_mem_H_of_mem_elementCentralizer {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a g u : G}
    (ha : a ∈ A) (hg : g ∈ elementCentralizer a) (hu : u ∈ H a) :
    conjBy g u ∈ H a := by
  let C := elementCentralizer a
  have hprod := h.centralizer_eq_product ha
  haveI : ((H a).subgroupOf C).Normal := by
    simpa [C] using internalSemidirectProduct_left_normal hprod
  have hmem :=
    Subgroup.Normal.conj_mem (show ((H a).subgroupOf C).Normal from inferInstance)
      (⟨u, hprod.left_le hu⟩ : C) hu (⟨g, hg⟩ : C)
  change (((⟨g, hg⟩ : C) * (⟨u, hprod.left_le hu⟩ : C) *
    (⟨g, hg⟩ : C)⁻¹ : C) : G) ∈ H a at hmem
  simpa [C, conjBy, mul_assoc] using hmem

private theorem conjBy_mem_cosetProduct_of_mem_elementCentralizer
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a g z : G}
    (ha : a ∈ A) (hg : g ∈ elementCentralizer a)
    (hz : z ∈ cosetProduct a (H a)) :
    conjBy g z ∈ cosetProduct a (H a) := by
  rcases hz with ⟨s, hs, u, hu, rfl⟩
  rw [Set.mem_singleton_iff] at hs
  subst s
  refine ⟨a, by simp, conjBy g u,
    conjBy_mem_H_of_mem_elementCentralizer h ha hg hu, ?_⟩
  calc
    conjBy g (a * u) = conjBy g a * conjBy g u := by
      simp [conjBy, mul_assoc]
    _ = a * conjBy g u := by
      rw [conjBy_eq_self_of_mem_elementCentralizer hg]

private theorem centralizer_le_coset_normalizer {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a : G} (ha : a ∈ A) :
    elementCentralizer a ≤ setNormalizer (cosetProduct a (H a)) := by
  intro g hg
  change normalizesSet (cosetProduct a (H a)) g
  intro z
  constructor
  · intro hgz
    have hz :=
      conjBy_mem_cosetProduct_of_mem_elementCentralizer h ha
        ((elementCentralizer a).inv_mem hg) hgz
    simpa [conjBy, mul_assoc] using hz
  · intro hz
    exact conjBy_mem_cosetProduct_of_mem_elementCentralizer h ha hg hz

private theorem conjBy_eq_base_of_mem_same_coset {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a g v : G}
    (ha : a ∈ A) (hv : v ∈ H a) (hga : conjBy g a = a * v) :
    conjBy g a = a := by
  let N := Nat.card (H a)
  have hvN : v ^ N = 1 := by
    dsimp [N]
    exact pow_natCard_subgroup_eq_one (H a) hv
  have haCL : a ∈ centralizerIn L a :=
    mem_centralizerIn_self (h.subset_L a ha)
  have horda : orderOf a ∣ Nat.card (centralizerIn L a) :=
    Subgroup.orderOf_dvd_natCard (centralizerIn L a) haCL
  have hN_order : Nat.Coprime N (orderOf a) := by
    dsimp [N]
    exact (h.coprime_orders ha ha).of_dvd_right horda
  rcases exists_pow_eq_self_of_coprime (x := a) hN_order with ⟨m, hm⟩
  have haNm : a ^ (N * m) = a := by
    simpa [pow_mul] using hm
  have hvNm : v ^ (N * m) = 1 := by
    rw [pow_mul, hvN]
    simp
  have hav_comm : Commute a v := by
    exact mem_elementCentralizer_commute ((h.centralizer_eq_product ha).left_le hv)
  have hav_pow : (a * v) ^ (N * m) = a := by
    calc
      (a * v) ^ (N * m) = a ^ (N * m) * v ^ (N * m) :=
        hav_comm.mul_pow (N * m)
      _ = a := by simp [haNm, hvNm]
  calc
    conjBy g a = conjBy g (a ^ (N * m)) := by rw [haNm]
    _ = conjBy g a ^ (N * m) := conjBy_pow g a (N * m)
    _ = (a * v) ^ (N * m) := by rw [hga]
    _ = a := hav_pow

private theorem coset_normalizer_le_centralizer {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Hypothesis2 A L H) {a : G} (ha : a ∈ A) :
    setNormalizer (cosetProduct a (H a)) ≤ elementCentralizer a := by
  intro g hg
  have hnorm : normalizesSet (cosetProduct a (H a)) g := by
    simpa [setNormalizer] using hg
  have ha_coset : a ∈ cosetProduct a (H a) := by
    refine ⟨a, by simp, 1, (H a).one_mem, ?_⟩
    simp
  have hga_coset : conjBy g a ∈ cosetProduct a (H a) :=
    (hnorm a).2 ha_coset
  rcases hga_coset with ⟨s, hs, v, hv, hga⟩
  rw [Set.mem_singleton_iff] at hs
  subst s
  have hfix : conjBy g a = a :=
    conjBy_eq_base_of_mem_same_coset h ha hv hga
  exact mem_elementCentralizer_of_conjBy_eq_self hfix

public theorem proposition_2_4 {G : Type u} [Group G] [Finite G]
    (A : Set G) (L : Subgroup G) (H : G → Subgroup G) :
    (Hypothesis2 A L H →
      ∀ ⦃a x : G⦄, a ∈ A → x ∈ L →
        H (conjBy x a) = conjugateSubgroup x (H a)) ∧
    (Hypothesis2 A L H →
      ∀ ⦃a b : G⦄, a ∈ A → b ∈ A →
        (conjugateSet (cosetProduct a (H a)) ∩
          conjugateSet (cosetProduct b (H b))).Nonempty →
          conjugateInSubgroup L a b) ∧
    (Hypothesis2 A L H →
      ∀ ⦃a : G⦄, a ∈ A →
        setNormalizer (cosetProduct a (H a)) = elementCentralizer a) := by
  constructor
  · intro h a x ha hx
    exact hFactor_conjugate_eq h ha hx
  constructor
  · intro h a b ha hb hinter
    rcases hinter with ⟨y, hyA, hyB⟩
    rcases hyA with ⟨au, hau_coset, hau_conj_y⟩
    rcases hyB with ⟨bv, hbv_coset, hbv_conj_y⟩
    rcases hau_coset with ⟨sa, hsa, u, hu, hau_eq⟩
    rw [Set.mem_singleton_iff] at hsa
    subst sa
    rcases hbv_coset with ⟨sb, hsb, v, hv, hbv_eq⟩
    rw [Set.mem_singleton_iff] at hsb
    subst sb
    subst au
    subst bv
    have hau_hbv : conjugateIn (a * u) (b * v) :=
      conjugateIn_trans hau_conj_y (conjugateIn_symm hbv_conj_y)
    have hab : conjugateIn a b :=
      conjugate_base_of_coset_conjugate h ha hb hu hv hau_hbv
    exact h.G_conjugate_imp_L_conjugate ha hb hab
  · intro h a ha
    exact le_antisymm
      (coset_normalizer_le_centralizer h ha)
      (centralizer_le_coset_normalizer h ha)

end CFSG.Section2

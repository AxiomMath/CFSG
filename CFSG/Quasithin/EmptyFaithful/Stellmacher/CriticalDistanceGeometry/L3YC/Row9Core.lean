module

import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.Quasithin.Stellmacher.CD.L3YC

open CFSG.Quasithin CFSG.QuasithinUnique

section Count

private theorem relIndex_sup_eq_of_le_normalizer' {G : Type*} [Group G] {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

theorem relIndex_mul_card_inf' {G : Type*} [Group G] (S A : Subgroup G) :
    S.relIndex A * Nat.card ↥(S ⊓ A) = Nat.card A := by
  have h1 : Nat.card (S.subgroupOf A) = Nat.card ↥(S ⊓ A) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [← h1]
  exact (S.subgroupOf A).index_mul_card

theorem card_sylow_two_pow {Hb : Type*} [Group Hb] [Finite Hb] {N X : Subgroup Hb}
    (hX : IsSylowTwoOf X N) {k o : ℕ} (ho : Odd o) (hN : Nat.card ↥N = 2 ^ k * o) :
    Nat.card ↥X = 2 ^ k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hX.2.1
  have hidx : ¬ 2 ∣ (X.subgroupOf N).index := hX.2.2
  have h1 : Nat.card ↥(X.subgroupOf N) * (X.subgroupOf N).index = Nat.card ↥N :=
    Subgroup.card_mul_index _
  have hXc : Nat.card ↥(X.subgroupOf N) = 2 ^ a := by
    rw [← ha]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX.1).toEquiv
  rw [hXc, hN] at h1
  rw [ha]
  have hoddI : Odd (X.subgroupOf N).index := Nat.odd_iff.mpr (by omega)
  have hcop1 : Nat.Coprime (2 ^ a) o :=
    (Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr ho))
  have hcop2 : Nat.Coprime (2 ^ k) (X.subgroupOf N).index :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hoddI))
  have hd1 : 2 ^ a ∣ 2 ^ k := by
    have : 2 ^ a ∣ 2 ^ k * o := ⟨(X.subgroupOf N).index, h1.symm⟩
    exact hcop1.dvd_of_dvd_mul_right this
  have hd2 : 2 ^ k ∣ 2 ^ a := by
    have : 2 ^ k ∣ 2 ^ a * (X.subgroupOf N).index := ⟨o, h1⟩
    exact hcop2.dvd_of_dvd_mul_right this
  have := Nat.dvd_antisymm hd1 hd2
  exact this

theorem two_pow_le_of_dvd {a c r C o : ℕ} (hr : r ∣ 168) (hC : C = 2 ^ c * o) (ho : Odd o)
    (h : 2 ^ a ∣ r * C) : 2 ^ a ≤ 8 * 2 ^ c := by
  have h1 : r * C ∣ (8 * 2 ^ c) * (21 * o) := by
    obtain ⟨t, ht⟩ := hr
    refine ⟨t, ?_⟩
    rw [hC]
    calc 8 * 2 ^ c * (21 * o) = 168 * 2 ^ c * o := by ring
      _ = (r * t) * 2 ^ c * o := by rw [ht]
      _ = r * (2 ^ c * o) * t := by ring
  have hcop : Nat.Coprime (2 ^ a) (21 * o) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact (by decide : Odd 21).mul ho
  have := hcop.dvd_of_dvd_mul_right (h.trans h1)
  exact Nat.le_of_dvd (by positivity) this

theorem card_isSL2_seven {X : Type} [Group X] (h : IsSL2 7 X) : Nat.card X = 336 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv,
    CFSG.OrderReductions.LinearOrders.card_specialLinear (ZMod 7) 2 (by norm_num),
    Nat.card_zmod]
  decide

end Count

section Core

variable {Hb : Type} [Group Hb] [Finite Hb]

theorem false_row9_core {S Lb L1b : Subgroup Hb} (hS : IsSylowTwoOf S ⊤) (hN : L1b.Normal)
    (hLL : Lb ≤ L1b)
    (hsplit : ∀ s ∈ S, ∃ p ∈ S ⊓ Lb, ∃ c ∈ S, (∀ x ∈ Lb, c * x * c⁻¹ = x) ∧ s = p * c)
    (hB : IsSL2 7 ↥Lb) {k o m : ℕ} (hk : Nat.card ↥L1b = 2 ^ k * o) (ho : Odd o)
    (hkm : 8 * m < 2 ^ k)
    (hC : ∀ z g : ↥L1b, z ∈ Lb.subgroupOf L1b → g ∈ Lb.subgroupOf L1b → z ^ 2 = 1 → z ≠ 1 →
      orderOf g = 7 → (∀ b ∈ Lb.subgroupOf L1b, b * z = z * b) →
      ∀ Q : Subgroup ↥L1b,
        Q ≤ Subgroup.centralizer ((Lb.subgroupOf L1b : Subgroup ↥L1b) : Set ↥L1b) →
        IsPGroup 2 Q → Nat.card ↥Q ≤ m) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B' : Subgroup ↥L1b := Lb.subgroupOf L1b with hB'
  set C' : Subgroup ↥L1b := Subgroup.centralizer (B' : Set ↥L1b) with hC'
  have hnorm : (⊤ : Subgroup Hb) ≤ Subgroup.normalizer (L1b : Set Hb) :=
    le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hN).symm
  have hX : IsSylowTwoOf (S ⊓ L1b) L1b := A4.isSylowTwoOf_inf_normal hS le_top hnorm
  have hXc : Nat.card ↥(S ⊓ L1b) = 2 ^ k := card_sylow_two_pow hX ho hk
  let P' : Subgroup ↥L1b := (S ⊓ L1b).subgroupOf L1b
  have hP'c : Nat.card ↥P' = 2 ^ k := by
    rw [← hXc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  obtain ⟨e0⟩ := hB
  let eB : ↥B' ≃* ↥Lb := Subgroup.subgroupOfEquivOfLe hLL
  let e : ↥B' ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) := eB.trans e0
  have hB'c : Nat.card ↥B' = 336 := by
    rw [Nat.card_congr e.toEquiv,
      ← card_isSL2_seven (X := Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) ⟨MulEquiv.refl _⟩]
  let z' : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
    ⟨!![(-1 : ZMod 7), 0; 0, -1], by rw [Matrix.det_fin_two_of]; decide⟩
  have hz'sq : z' ^ 2 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, z'] <;> decide
  have hz'ne : z' ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 0) h
    have h2 : (-1 : ZMod 7) = 1 := by simpa [z'] using this
    exact absurd h2 (by decide)
  have hz'c : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7), g * z' = z' * g := by
    intro g
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, z'] <;> ring
  let zB : ↥B' := e.symm z'
  have hzBsq : zB ^ 2 = 1 := by rw [← map_pow, hz'sq, map_one]
  have hzBne : zB ≠ 1 := fun h => hz'ne (by simpa [zB] using congrArg e h)
  have hzBc : ∀ b : ↥B', b * zB = zB * b := fun b => by
    apply e.injective
    simp only [map_mul, zB, MulEquiv.apply_symm_apply]
    exact hz'c _
  obtain ⟨gB, hgB⟩ : ∃ gB : ↥B', orderOf gB = 7 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact exists_prime_orderOf_dvd_card' (G := ↥B') 7 (by rw [hB'c]; norm_num)
  set z : ↥L1b := (zB : ↥L1b) with hzdef
  set g : ↥L1b := (gB : ↥L1b) with hgdef
  have hz2 : z ^ 2 = 1 := by
    have := congrArg Subtype.val hzBsq
    simpa [z] using this
  have hz1 : z ≠ 1 := fun h => hzBne (Subtype.ext h)
  have hgord : orderOf g = 7 := by
    rw [← hgB]; exact Subgroup.orderOf_coe gB
  have hzc : ∀ b ∈ B', b * z = z * b := fun b hb => by
    have := congrArg Subtype.val (hzBc ⟨b, hb⟩)
    simpa [z] using this
  have hQ := hC z g zB.2 gB.2 hz2 hz1 hgord hzc
  have hPle : P' ≤ B' ⊔ C' := by
    rintro ⟨s, hsL⟩ hs
    have hs' : s ∈ S ⊓ L1b := hs
    obtain ⟨p, hp, c, hc, hcent, hsp⟩ := hsplit s hs'.1
    have hpL : p ∈ L1b := hLL hp.2
    have hcL : c ∈ L1b := by
      have : p⁻¹ * s ∈ L1b := L1b.mul_mem (L1b.inv_mem hpL) hsL
      rw [show c = p⁻¹ * s by rw [hsp]; group]
      exact this
    have hpB : (⟨p, hpL⟩ : ↥L1b) ∈ B' := hp.2
    have hcC : (⟨c, hcL⟩ : ↥L1b) ∈ C' := by
      rw [hC', Subgroup.mem_centralizer_iff]
      intro h hh
      apply Subtype.ext
      have hh' : (h : Hb) ∈ Lb := hh
      have := hcent (h : Hb) hh'
      show (h : Hb) * c = c * (h : Hb)
      calc (h : Hb) * c = (c * h * c⁻¹) * c := by rw [this]
        _ = c * h := by group
    have : (⟨s, hsL⟩ : ↥L1b) = ⟨p, hpL⟩ * ⟨c, hcL⟩ := Subtype.ext hsp
    rw [this]
    exact Subgroup.mul_mem_sup hpB hcC
  have key : ∀ b ∈ B', ∀ k ∈ C', b * k * b⁻¹ = k := by
    intro b hb k hk
    rw [hC', Subgroup.mem_centralizer_iff] at hk
    calc b * k * b⁻¹ = (k * b) * b⁻¹ := by rw [hk b hb]
      _ = k := by group
  have hBN : B' ≤ Subgroup.normalizer (C' : Set ↥L1b) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; rw [key b hb h hh]; exact hh
    · intro hh
      have h1 := key b⁻¹ (B'.inv_mem hb) _ hh
      have h2 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ = h := by group
      rw [h2] at h1
      rw [h1]; exact hh
  have hB'cardLe : ∀ x : ℕ, True := fun _ => trivial
  have hr : C'.relIndex B' ∣ 168 := by
    have h4 := relIndex_mul_card_inf' C' B'
    have h5 : 2 ∣ Nat.card ↥(C' ⊓ B') := by
      have hzC : z ∈ C' := by
        rw [hC', Subgroup.mem_centralizer_iff]
        exact fun h hh => hzc h hh
      have hzmem : z ∈ C' ⊓ B' := ⟨hzC, zB.2⟩
      have hle : Subgroup.zpowers z ≤ C' ⊓ B' := (Subgroup.zpowers_le).mpr hzmem
      have hcard := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, orderOf_eq_prime hz2 hz1] at hcard
    obtain ⟨d', hd'⟩ := h5
    rw [hd', hB'c] at h4
    exact ⟨d', by linarith⟩
  obtain ⟨Q0⟩ : Nonempty (Sylow 2 ↥C') := inferInstance
  have hQcard : Nat.card ↥Q0 = 2 ^ (Nat.card ↥C').factorization 2 := Q0.card_eq_multiplicity
  let Q : Subgroup ↥L1b := (Q0 : Subgroup ↥C').map C'.subtype
  have hQC : Nat.card ↥Q = 2 ^ (Nat.card ↥C').factorization 2 := by
    rw [← hQcard]
    exact Subgroup.card_map_of_injective C'.subtype_injective
  have hQp : IsPGroup 2 ↥Q := IsPGroup.of_card hQC
  have hQm := hQ Q (Subgroup.map_subtype_le _) hQp
  rw [hQC] at hQm
  have hCc : Nat.card ↥C' = 2 ^ (Nat.card ↥C').factorization 2 *
      (Nat.card ↥C' / 2 ^ (Nat.card ↥C').factorization 2) :=
    (Nat.ordProj_mul_ordCompl_eq_self _ 2).symm
  have ho' : Odd (Nat.card ↥C' / 2 ^ (Nat.card ↥C').factorization 2) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two Nat.card_pos.ne')
  have hD : Nat.card ↥(B' ⊔ C') = C'.relIndex B' * Nat.card ↥C' := by
    have h1 := relIndex_mul_card_inf' C' (B' ⊔ C')
    rw [inf_eq_left.mpr le_sup_right, relIndex_sup_eq_of_le_normalizer' hBN] at h1
    exact h1.symm
  have hdvd : 2 ^ k ∣ C'.relIndex B' * Nat.card ↥C' := by
    rw [← hD, ← hP'c]
    exact Subgroup.card_dvd_of_le hPle
  have hle := two_pow_le_of_dvd hr hCc ho' hdvd
  omega

end Core

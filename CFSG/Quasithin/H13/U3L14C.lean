module

public import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_centralizer_le {x : G} {X P : Subgroup G} (h : X ≤ P) :
    (centralizer ({x} : Set G)).relIndex X ≤ (centralizer ({x} : Set G)).relIndex P :=
  relIndex_le_of_le_right h
    (index_ne_zero_of_finite (H := (centralizer ({x} : Set G)).subgroupOf P))

theorem relIndex_centralizer_modEq_one {x : G} {P : Subgroup G} (hx : x ^ 3 = 1)
    (hxP : x ∈ normalizer (P : Set G)) (hP : IsPGroup 2 P) :
    (centralizer ({x} : Set G)).relIndex P ≡ 1 [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥P := Fintype.ofFinite _
  set C := (centralizer ({x} : Set G)).subgroupOf P with hC
  let f : Function.End ↥P := fun p => ⟨x * p * x⁻¹, (mem_normalizer_iff.mp hxP p).mp p.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext p
    apply Subtype.ext
    show x * (x * (x * (p : G) * x⁻¹) * x⁻¹) * x⁻¹ = p
    have hx' : x * x * x = 1 := by rw [← hx, pow_three, mul_assoc]
    have : x * (x * (x * (p : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * p * (x * x * x)⁻¹ := by
      group
    rw [this, hx']
    group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = Nat.card C := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun p => ?_)
    rw [Function.mem_fixedPoints, Function.IsFixedPt, hC, mem_subgroupOf,
      mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : x * (p : G) * x⁻¹ = p := congrArg Subtype.val h
      calc (p : G) * x = x * p * x⁻¹ * x := by rw [h1]
        _ = x * p := by group
    · intro h
      apply Subtype.ext
      show x * (p : G) * x⁻¹ = p
      rw [← h]
      group
  rw [hfix, ← Nat.card_eq_fintype_card] at hmod
  have hcard : Nat.card ↥P = Nat.card C * C.index := (card_mul_index C).symm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hP.to_subgroup C)
  have hcop : Nat.Coprime 3 (Nat.card C) := by
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  rw [hcard] at hmod
  have h2 : Nat.card C * C.index ≡ Nat.card C * 1 [MOD 3] := by rwa [mul_one]
  exact Nat.ModEq.cancel_left_of_coprime hcop.gcd_eq_one h2

theorem four_le_relIndex_centralizer {x : G} {P : Subgroup G} (hx : x ^ 3 = 1)
    (hxP : x ∈ normalizer (P : Set G)) (hP : IsPGroup 2 P)
    (h : ¬ P ≤ centralizer ({x} : Set G)) :
    4 ≤ (centralizer ({x} : Set G)).relIndex P := by
  have hmod := relIndex_centralizer_modEq_one hx hxP hP
  have hdvd : (centralizer ({x} : Set G)).relIndex P ∣ Nat.card ↥P := index_dvd_card _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  rw [hn] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h1 : (centralizer ({x} : Set G)).relIndex P ≠ 1 := fun h1 =>
    h (relIndex_eq_one.mp h1)
  rw [hk] at hmod h1 ⊢
  rcases k with _ | _ | k
  · exact absurd (pow_zero 2) h1
  · exact absurd hmod (by decide)
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem relIndex_centralizer_eq_mul {x : G} {N P : Subgroup G} (hNP : N ≤ P)
    (hPN : P ≤ normalizer (N : Set G)) :
    (centralizer ({x} : Set G)).relIndex P =
      (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P *
        (centralizer ({x} : Set G)).relIndex N := by
  generalize centralizer ({x} : Set G) = C
  have hHN : P ⊓ C ≤ normalizer (N : Set G) := inf_le_left.trans hPN
  have hcard : ∀ {A B : Subgroup G}, A ≤ B → Nat.card ↥B = Nat.card ↥A * A.relIndex B :=
    fun {A B} hAB => by
      rw [← Nat.card_congr (subgroupOfEquivOfLe hAB).toEquiv]
      exact (card_mul_index _).symm
  have e1 := hcard (le_sup_left : N ≤ N ⊔ (P ⊓ C))
  have e4 := hcard (le_sup_right : P ⊓ C ≤ N ⊔ (P ⊓ C))
  have e2 : N.relIndex (N ⊔ (P ⊓ C)) = (N ⊓ (P ⊓ C)).relIndex (P ⊓ C) := by
    rw [sup_comm, inf_relIndex_right]
    have := Subgroup.normal_subgroupOf_of_le_normalizer hHN
    have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hHN
    exact Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient (P ⊓ C) N hHN).toEquiv.symm
  have e3 := hcard (inf_le_right : N ⊓ (P ⊓ C) ≤ P ⊓ C)
  have e5 := hcard (inf_le_left : N ⊓ (P ⊓ C) ≤ N)
  have hNHC : N ⊓ (P ⊓ C) = C ⊓ N := by
    rw [inf_comm P C, ← inf_assoc, inf_comm N C, inf_assoc, inf_eq_left.mpr hNP]
  have hrel : C.relIndex P = (P ⊓ C).relIndex P := by rw [inf_comm, inf_relIndex_right]
  have hrel2 : C.relIndex N = (N ⊓ (P ⊓ C)).relIndex N := by rw [hNHC, inf_relIndex_right]
  have hmul := relIndex_mul_relIndex (P ⊓ C) (N ⊔ (P ⊓ C)) P le_sup_right
    (sup_le hNP inf_le_left)
  rw [hrel, ← hmul, hrel2, mul_comm]
  congr 1
  have hpos : 0 < Nat.card ↥(N ⊓ (P ⊓ C)) * (N ⊓ (P ⊓ C)).relIndex (P ⊓ C) := by
    rw [← e3]
    exact Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.card ↥(N ⊓ (P ⊓ C)) * (N ⊓ (P ⊓ C)).relIndex (P ⊓ C) *
        (P ⊓ C).relIndex (N ⊔ (P ⊓ C))
      = Nat.card ↥(N ⊔ (P ⊓ C)) := by rw [← e3, ← e4]
    _ = Nat.card ↥N * (N ⊓ (P ⊓ C)).relIndex (P ⊓ C) := by rw [e1, e2]
    _ = Nat.card ↥(N ⊓ (P ⊓ C)) * (N ⊓ (P ⊓ C)).relIndex (P ⊓ C) *
        (N ⊓ (P ⊓ C)).relIndex N := by rw [e5]; ring

theorem sup_inf_centralizer_eq {x : G} {N P : Subgroup G} (hx : x ^ 3 = 1)
    (hN : IsPGroup 2 N) (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set G))
    (hxN : x ∈ normalizer (N : Set G)) (h : ∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ N) :
    N ⊔ (P ⊓ centralizer ({x} : Set G)) = P := by
  refine le_antisymm (sup_le hNP inf_le_left) fun p hp => ?_
  set H := normalizer (N : Set G) with hHdef
  have hNn : (N.subgroupOf H).Normal := Subgroup.normal_in_normalizer
  have hcop : Nat.Coprime 3 (Nat.card ↥(N.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hN
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have ha : (⟨x, hxN⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hx)
  obtain ⟨y, hy1, hy2⟩ := CFSG.SignalizerFunctorTheorem.exists_fixed_of_coprime Nat.prime_three ha
    (N.subgroupOf H) hcop (w := ⟨p, hPN hp⟩) (by
      rw [mem_subgroupOf]
      simpa using h p hp)
  have hyN : (y : G) * p⁻¹ ∈ N := by simpa using mem_subgroupOf.mp hy1
  have hyP : (y : G) ∈ P := by
    have : (y : G) = ((y : G) * p⁻¹) * p := by group
    rw [this]
    exact mul_mem (hNP hyN) hp
  have hyx : (y : G) ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : x * (y : G) * x⁻¹ = y := by simpa using congrArg Subtype.val hy2
    calc (y : G) * x = x * y * x⁻¹ * x := by rw [h1]
      _ = x * y := by group
  have : p = ((y : G) * p⁻¹)⁻¹ * y := by group
  rw [this]
  exact mul_mem (mem_sup_left (inv_mem hyN)) (mem_sup_right ⟨hyP, hyx⟩)

theorem relIndex_sup_modEq_one {x : G} {N P : Subgroup G} (hx : x ^ 3 = 1)
    (hP : IsPGroup 2 P) (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set G))
    (hxN : x ∈ normalizer (N : Set G)) (hxP : x ∈ normalizer (P : Set G)) :
    (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P ≡ 1 [MOD 3] := by
  set r := (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P with hr
  have hmul := relIndex_centralizer_eq_mul (x := x) hNP hPN
  have h1 := relIndex_centralizer_modEq_one hx hxP hP
  have h2 := relIndex_centralizer_modEq_one hx hxN (hP.to_le hNP)
  have h3 : r * (centralizer ({x} : Set G)).relIndex N ≡ 1 * 1 [MOD 3] := by
    rw [← hmul]
    simpa using h1
  have h4 : r * (centralizer ({x} : Set G)).relIndex N ≡ r * 1 [MOD 3] :=
    Nat.ModEq.mul_left r h2
  have h5 := h4.symm.trans h3
  simpa using h5

theorem relIndex_sup_eq_one_or {x : G} {N P : Subgroup G} (hx : x ^ 3 = 1)
    (hP : IsPGroup 2 P) (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set G))
    (hxN : x ∈ normalizer (N : Set G)) (hxP : x ∈ normalizer (P : Set G)) :
    (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P = 1 ∨
      4 ≤ (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P := by
  have hr3 := relIndex_sup_modEq_one hx hP hNP hPN hxN hxP
  have hdvd : (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P ∣ Nat.card ↥P := index_dvd_card _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  rw [hn] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk] at hr3 ⊢
  rcases k with _ | _ | k
  · left
    rfl
  · exact absurd hr3 (by decide)
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem relIndex_sup_le_four {x : G} {N P : Subgroup G} (hx : x ^ 3 = 1)
    (hP : IsPGroup 2 P) (hNP : N ≤ P) (hPN : P ≤ normalizer (N : Set G))
    (hxN : x ∈ normalizer (N : Set G)) (hxP : x ∈ normalizer (P : Set G))
    (h8 : N.relIndex P ≤ 8) :
    (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P ≤ 4 := by
  set r := (N ⊔ (P ⊓ centralizer ({x} : Set G))).relIndex P with hr
  have hmul := relIndex_centralizer_eq_mul (x := x) hNP hPN
  have h1 := relIndex_centralizer_modEq_one hx hxP hP
  have h2 := relIndex_centralizer_modEq_one hx hxN (hP.to_le hNP)
  have hr3 : r ≡ 1 [MOD 3] := by
    have h3 : r * (centralizer ({x} : Set G)).relIndex N ≡ 1 * 1 [MOD 3] := by
      rw [← hmul]
      simpa using h1
    have h4 : r * (centralizer ({x} : Set G)).relIndex N ≡ r * 1 [MOD 3] :=
      Nat.ModEq.mul_left r h2
    have h5 := h4.symm.trans h3
    simpa using h5
  have hdvd : r ∣ N.relIndex P := relIndex_dvd_of_le_left P le_sup_left
  have hdvd2 : N.relIndex P ∣ Nat.card ↥P := index_dvd_card _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  rw [hn] at hdvd2
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (hdvd.trans hdvd2)
  have hle : r ≤ 8 := (Nat.le_of_dvd (Nat.pos_of_ne_zero (by
    intro h0
    exact absurd h0 (index_ne_zero_of_finite (H := N.subgroupOf P)))) hdvd).trans h8
  rw [hk] at hr3 hle ⊢
  rcases k with _ | _ | _ | _ | k
  · norm_num
  · exact absurd hr3 (by decide)
  · norm_num
  · exact absurd hr3 (by decide)
  · have : 2 ^ 4 ≤ 2 ^ (k + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

end CFSG.Quasithin.H13.U3

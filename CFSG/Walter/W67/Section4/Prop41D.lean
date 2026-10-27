module

import CFSG.Walter.W67.Section4.Prop41A
import CFSG.Walter.W67.Section4.Prop41B
import CFSG.Walter.W67.Section4.Prop41C
import CFSG.Walter.W67.Section4.Prop43ab
import CFSG.Walter.W67.W2Cor32A
import CFSG.Walter.W67.W2Lemma26B
import CFSG.Walter.W67.Section4.Cor44
public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Walter.ReeOrder.JT.Section2
public import CFSG.Walter.W67.Interface

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commute_of_prime_order [Finite G] {ℓ : ℕ} (hℓ : ℓ.Prime) {z y : G} (hz : orderOf z = ℓ)
    (hyz : y * z * y⁻¹ ∈ Subgroup.zpowers z) {k : ℕ} (hy : orderOf y = ℓ ^ k) :
    y * z * y⁻¹ = z := by
  have : y * z * y⁻¹ ∈ (Submonoid.powers z : Set G) := by rw [powers_eq_zpowers]; exact hyz
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp this
  have hiter : ∀ j : ℕ, y ^ j * z * (y ^ j)⁻¹ = z ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc y ^ (j + 1) * z * (y ^ (j + 1))⁻¹ = y * (y ^ j * z * (y ^ j)⁻¹) * y⁻¹ := by
            rw [pow_succ']; group
        _ = y * z ^ (m ^ j) * y⁻¹ := by rw [ih]
        _ = (y * z * y⁻¹) ^ (m ^ j) := by rw [conj_pow]
        _ = z ^ (m ^ (j + 1)) := by rw [← hm, ← pow_mul, pow_succ']
  have h1 := hiter (ℓ ^ k)
  have hyk : y ^ ℓ ^ k = 1 := hy ▸ pow_orderOf_eq_one y
  rw [hyk, one_mul, inv_one, mul_one] at h1
  have h2 : 1 ≡ m ^ ℓ ^ k [MOD orderOf z] :=
    pow_eq_pow_iff_modEq.mp (by rw [pow_one]; exact h1)
  rw [hz] at h2
  have h3 : m % ℓ = 1 % ℓ := by
    rw [← pow_prime_pow_mod hℓ m k]
    exact h2.symm
  rw [← hm]
  have h4 : z ^ m = z ^ 1 := (pow_eq_pow_iff_modEq.mpr (by rw [hz]; exact h3))
  rw [h4, pow_one]

namespace Std

variable (s : Std G)

theorem odd_card_centralizer_K {ℓ : ℕ} [Fact ℓ.Prime]
    (h4 : (s.q % 4 = 3 → ¬ ℓ ∣ s.q + 1) ∧ (s.q % 4 = 1 → ¬ ℓ ∣ s.q - 1)) {z : G}
    (hzK : z ∈ s.K) (hz : orderOf z = ℓ) :
    Odd (Nat.card (s.K ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := (s.K ⊓ Subgroup.centralizer ({z} : Set G) : Subgroup G)) 2 hev.two_dvd
  have htK : (t : G) ∈ s.K := t.2.1
  have htz : (t : G) * z = z * t :=
    (Subgroup.mem_centralizer_singleton_iff.mp t.2.2)
  set t' : s.K := ⟨t, htK⟩
  set z' : s.K := ⟨z, hzK⟩
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, ht]
  have hzC : z' ∈ Subgroup.centralizer ({t'} : Set s.K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext htz.symm
  have hdvd : ℓ ∣ Nat.card (Subgroup.centralizer ({t'} : Set s.K)) := by
    rw [← hz, ← Subgroup.orderOf_mk z hzK]
    exact Subgroup.orderOf_dvd_natCard _ hzC
  have hKcard : Nat.card (GaloisField s.p s.f) = s.p ^ s.f :=
    GaloisField.card _ _ s.f_pos.ne'
  obtain ⟨h1, h3⟩ := psl2_centralizer_involution (GaloisField s.p s.f) hKcard s.odd_p s.f_pos
    (t := s.iso t') (by rw [MulEquiv.orderOf_eq, ht'2])
  have hmap := CFSG.centralizer_singleton_map s.iso t'
  have hcard : Nat.card (Subgroup.centralizer ({t'} : Set s.K)) =
      Nat.card (Subgroup.centralizer ({s.iso t'} : Set PSL(2, GaloisField s.p s.f))) := by
    rw [← hmap, Subgroup.card_map_of_injective s.iso.injective]
  have hq := Nat.odd_iff.mp (s.odd_p.pow (n := s.f))
  have hq4 : s.q % 4 = 1 ∨ s.q % 4 = 3 := by
    change s.p ^ s.f % 4 = 1 ∨ s.p ^ s.f % 4 = 3
    omega
  rcases hq4 with hq4 | hq4
  · obtain ⟨hc, -⟩ := h1 hq4
    rw [hcard, hc] at hdvd
    exact h4.2 hq4 hdvd
  · obtain ⟨hc, -⟩ := h3 hq4
    rw [hcard, hc] at hdvd
    exact h4.1 hq4 hdvd

theorem factorization_two_centralizer
    {ℓ : ℕ} [Fact ℓ.Prime]
    (h4 : (s.q % 4 = 3 → ¬ ℓ ∣ s.q + 1) ∧ (s.q % 4 = 1 → ¬ ℓ ∣ s.q - 1)) {z : G}
    (hzK : z ∈ s.K) (hz : orderOf z = ℓ) :
    (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 2 ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({z} : Set G) with hC
  have hJC : s.J ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    (s.commute_J (s.K_le_H hzK)).symm
  set Y := (s.K ⊔ s.fr.E) ⊓ C with hY
  have hEN : s.fr.E ≤ Subgroup.normalizer (s.K : Set G) := s.fr.E_le_H.trans s.H_le_normalizer
  have hKEH : s.K ⊔ s.fr.E ≤ s.H := sup_le s.K_le_H s.fr.E_le_H
  have hYodd : Odd (Nat.card Y) := by
    have hYN : Y ≤ Subgroup.normalizer (s.K : Set G) :=
      (inf_le_left.trans hKEH).trans s.H_le_normalizer
    have hc := card_sup_mul_card_inf_of_le_normalizer hYN
    have hc2 := card_sup_mul_card_inf_of_le_normalizer hEN
    rw [s.fr.K_inf_E, Subgroup.card_bot, mul_one] at hc2
    have hdvd : Nat.card (s.K ⊔ Y : Subgroup G) ∣ Nat.card (s.K ⊔ s.fr.E : Subgroup G) :=
      Subgroup.card_dvd_of_le (sup_le le_sup_left inf_le_left)
    have hKY : s.K ⊓ Y = s.K ⊓ C := by
      rw [hY, ← inf_assoc, inf_eq_left.mpr (le_sup_left : s.K ≤ s.K ⊔ s.fr.E)]
    have hKYodd : Odd (Nat.card (s.K ⊓ Y : Subgroup G)) := by
      rw [hKY]
      exact s.odd_card_centralizer_K h4 hzK hz
    have h1 : Nat.card s.K * Nat.card Y ∣
        Nat.card s.K * (Nat.card s.fr.E * Nat.card (s.K ⊓ Y : Subgroup G)) := by
      rw [← hc, ← mul_assoc, ← hc2]
      exact Nat.mul_dvd_mul_right hdvd _
    have h2 := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1
    exact Odd.of_dvd_nat (s.fr.odd_card_E.mul hKYodd) h2
  have hCH : C ⊓ s.H ≤ Subgroup.zpowers s.J ⊔ Y := by
    rintro h ⟨hhC, hhH⟩
    obtain ⟨j, hj, k, hk, e, he, rfl⟩ := s.fr.exists_decomp_H hhH
    have hjC : j ∈ C := (Subgroup.zpowers_le.mpr hJC) hj
    have hke : k * e ∈ Y := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right he), ?_⟩
      have := C.mul_mem (C.inv_mem hjC) hhC
      rwa [show j⁻¹ * (j * k * e) = k * e by group] at this
    rw [mul_assoc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hke)
  have hc : ∀ x ∈ Subgroup.zpowers s.J, ∀ y ∈ Y, x * y = y * x := by
    intro x hx y hy
    have hyH : y ∈ s.H := hKEH hy.1
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (s.commute_J hyH).symm n)).eq
  obtain ⟨hc1, -⟩ := card_sup_mul_card_inf_of_commute _ _ hc
  rw [s.card_zpowers_J] at hc1
  have hJ2 : IsPGroup 2 (Subgroup.zpowers (⟨s.J, hJC⟩ : C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, s.orderOf_J,
      pow_one])
  obtain ⟨Q, hQ⟩ := hJ2.exists_le_sylow
  set Q' := (Q : Subgroup C).map C.subtype with hQ'
  have hQ'2 : IsPGroup 2 Q' := Q.isPGroup'.map _
  have hJQ' : s.J ∈ Q' := ⟨⟨s.J, hJC⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  have hab := s.isMulCommutative_of_isPGroup hQ'2
  have hQ'H : Q' ≤ C ⊓ s.H := fun x hx =>
    ⟨Subgroup.map_subtype_le _ hx, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨s.J, hJQ'⟩))⟩
  have hQcard : Nat.card Q' ∣ 2 * Nat.card Y := by
    have h1 := Subgroup.card_dvd_of_le (hQ'H.trans hCH)
    exact h1.trans (Dvd.intro _ hc1)
  obtain ⟨k, hk⟩ := hQ'2.exists_card_eq
  have hQc : Nat.card (Q : Subgroup C) = Nat.card Q' := by
    rw [hQ', Subgroup.card_map_of_injective C.subtype_injective]
  have hk1 : k ≤ 1 := by
    rw [hk] at hQcard
    by_contra hk2
    push Not at hk2
    have h4' : 2 ^ 2 ∣ 2 * Nat.card Y := (pow_dvd_pow 2 hk2).trans hQcard
    obtain ⟨c, hc'⟩ := h4'
    have : Even (Nat.card Y) := ⟨c, by omega⟩
    exact (Nat.not_even_iff_odd.mpr hYodd) this
  have := Q.card_eq_multiplicity
  rw [hQc, hk] at this
  have := Nat.pow_right_injective (le_refl 2) this
  omega

end Std

theorem exists_sylow_le_of_le {ℓ : ℕ} [Fact ℓ.Prime] {Q Y : Subgroup G} (hQY : Q ≤ Y)
    (hQ : IsPGroup ℓ Q) :
    ∃ P : Subgroup G, Q ≤ P ∧ P ≤ Y ∧ IsPGroup ℓ P ∧
      Nat.card P = ℓ ^ (Nat.card Y).factorization ℓ := by
  have hQ' : IsPGroup ℓ (Q.subgroupOf Y) := hQ.comap_subtype
  obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
  refine ⟨(S : Subgroup Y).map Y.subtype, fun x hx => ⟨⟨x, hQY hx⟩,
    hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩, Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, S.card_eq_multiplicity]

theorem exists_mem_center_orderOf {ℓ : ℕ} [Fact ℓ.Prime] {P : Subgroup G} (hP : IsPGroup ℓ P)
    (hne : P ≠ ⊥) : ∃ z ∈ P ⊓ Subgroup.centralizer (P : Set G), orderOf z = ℓ := by
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  have := hP.center_nontrivial
  obtain ⟨c, hc⟩ := exists_ne (1 : Subgroup.center P)
  have hcZ : ((c : P) : G) ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
    refine ⟨(c : P).2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩)
  have hZℓ : IsPGroup ℓ (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
    hP.to_le inf_le_left
  have hZne : (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) ≠ ⊥ := by
    intro h
    rw [h] at hcZ
    exact hc (Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hcZ)))
  obtain ⟨k, hk⟩ := hZℓ.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hZne (Subgroup.card_eq_one.mp hk)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) ℓ (hk ▸ dvd_pow_self ℓ hk0)
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz]⟩

namespace Std

variable (s : Std G)

theorem center_le_K
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓp : ℓ ≠ s.p)
    (hℓK : ℓ ∣ Nat.card s.K) {P₀ P : Subgroup G} (hP₀E : P₀ ≤ s.fr.E)
    (hP₀card : Nat.card P₀ = ℓ ^ (Nat.card s.fr.E).factorization ℓ) (hPH : P ≤ s.H)
    (hPℓ : IsPGroup ℓ P) (hPcard : Nat.card P = ℓ ^ (Nat.card s.H).factorization ℓ)
    (hP₀P : P₀ ≤ P) : P ⊓ Subgroup.centralizer (P : Set G) ≤ s.K := by
  have hℓ : ℓ.Prime := Fact.out
  rintro x ⟨hxP, hxC⟩
  have hsup := s.sup_eq hℓ2 hP₀E hP₀card hPH hPℓ hPcard hP₀P
  have hN : P₀ ≤ Subgroup.normalizer ((P ⊓ s.K : Subgroup G) : Set G) := fun z hz =>
    normalizer_inf_normalizer_le P s.K ⟨Subgroup.le_normalizer (hP₀P hz),
      s.H_le_normalizer (hPH (hP₀P hz))⟩
  have hx' : x ∈ (P ⊓ s.K) ⊔ P₀ := by rw [hsup]; exact hxP
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hx'
  have hcyc : IsCyclic (P ⊓ s.K : Subgroup G) :=
    s.psl2Facts_K.cyclic ℓ hℓ hℓ2 hℓp _ inf_le_right (hPℓ.to_le inf_le_left)
  have hbC : ∀ y ∈ P ⊓ s.K, y * b = b * y := by
    intro y hy
    have hay : a * y = y * a := congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := (P ⊓ s.K : Subgroup G))).is_comm.comm ⟨a, ha⟩ ⟨y, hy⟩)
    have hxy : y * (a * b) = (a * b) * y := Subgroup.mem_centralizer_iff.mp hxC y hy.1
    calc y * b = a⁻¹ * (a * y) * b := by group
      _ = a⁻¹ * (y * a) * b := by rw [hay]
      _ = a⁻¹ * (y * (a * b)) := by group
      _ = a⁻¹ * ((a * b) * y) := by rw [hxy]
      _ = b * y := by group
  by_contra hab
  have hb1 : b ≠ 1 := by
    intro h
    apply hab
    rw [h, mul_one]
    exact ha.2
  have hbℓ : IsPGroup ℓ (Subgroup.zpowers b) := hPℓ.to_le (Subgroup.zpowers_le.mpr (hP₀P hb))
  obtain ⟨k, hk⟩ := hbℓ.exists_card_eq
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Nat.card_zpowers] at hk
    exact hb1 (orderOf_eq_one_iff.mp hk)
  obtain ⟨b', hb'⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers b) ℓ
    (hk ▸ dvd_pow_self ℓ hk0)
  have hΩb : Subgroup.zpowers (b' : G) ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr b'.2
  have hΩE : Subgroup.zpowers (b' : G) ≤ s.fr.E := hΩb.trans (Subgroup.zpowers_le.mpr (hP₀E hb))
  have hΩcard : Nat.card (Subgroup.zpowers (b' : G)) = ℓ := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hb']
  have hle : P ⊓ s.K ≤ s.KX (Subgroup.zpowers (b' : G)) := by
    intro y hy
    refine ⟨hy.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hΩb hw)
    exact (Commute.zpow_left (hbC y hy).symm n).eq
  refine s.not_pow_dvd_card_KX hℓ2 hℓp hℓK hΩE hΩcard ?_
  rw [← s.card_inf_K hℓ2 hPH hPℓ hPcard]
  exact Subgroup.card_dvd_of_le hle

theorem false_of_odd_torus
    (hJ : s.p ≠ 3 → JFacts) (hR : RFacts) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓσ : ℓ ∈ s.fr.σ) (hℓp : ℓ ≠ s.p)
    (h3 : s.p = 3 → ℓ ≠ 3 ∧ ¬ ℓ ∣ s.q ^ 2 - s.q + 1)
    (h5 : s.p = 5 → ℓ ≠ 7 ∧ ℓ ≠ 11 ∧ ℓ ≠ 19)
    (h4 : (s.q % 4 = 3 → ¬ ℓ ∣ s.q + 1) ∧ (s.q % 4 = 1 → ¬ ℓ ∣ s.q - 1)) : False := by
  have hℓ : ℓ.Prime := Fact.out
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hℓE : ℓ ∣ Nat.card s.fr.E := (Nat.mem_primeFactors.mp hℓσ).2.1
  have hℓ2 : ℓ ≠ 2 := fun h => by
    subst h
    exact (Nat.not_even_iff_odd.mpr s.fr.odd_card_E) (even_iff_two_dvd.mpr hℓE)
  have hℓK := s.dvd_card_K hJ hR hℓσ h3 h5
  obtain ⟨P₀, hP₀E, hP₀ℓ, hP₀ne, hP₀card⟩ := s.exists_sylow_E hℓE
  obtain ⟨Q₀, -, hQ₀K, hQ₀ℓ, hQ₀card⟩ :=
    exists_sylow_le_of_le (bot_le : ⊥ ≤ s.KX P₀) (IsPGroup.of_bot (p := ℓ))
  have hP₀C : P₀ ≤ Subgroup.centralizer (P₀ : Set G) := fun x hx =>
    s.E_le_centralizer hP₀E (hP₀E hx)
  have hQ₀C : Q₀ ≤ Subgroup.centralizer (P₀ : Set G) := hQ₀K.trans inf_le_right
  have hP₀N : P₀ ≤ Subgroup.normalizer (Q₀ : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_iff.mp (hQ₀C hy) x hx).symm)
  have hc := card_sup_mul_card_inf_of_le_normalizer hP₀N
  have hinf : Q₀ ⊓ P₀ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : x ∈ s.K ⊓ s.fr.E := ⟨(hQ₀K hx1).1, hP₀E hx2⟩
    rwa [s.fr.K_inf_E] at this
  rw [hinf, Subgroup.card_bot, mul_one, hQ₀card, hP₀card, ← pow_add] at hc
  have hQP : IsPGroup ℓ (Q₀ ⊔ P₀ : Subgroup G) := IsPGroup.of_card hc
  have hQPH : Q₀ ⊔ P₀ ≤ s.H :=
    sup_le ((hQ₀K.trans inf_le_left).trans s.K_le_H) (hP₀E.trans s.fr.E_le_H)
  obtain ⟨P, hQPP, hPH, hPℓ, hPcard⟩ := exists_sylow_le_of_le hQPH hQP
  have hP₀P : P₀ ≤ P := le_sup_right.trans hQPP
  have hsyl : (Nat.card (Subgroup.normalizer (P₀ : Set G))).factorization ℓ ≤
      (Nat.card (P ⊓ Subgroup.centralizer (P₀ : Set G) : Subgroup G)).factorization ℓ := by
    have h1 := s.factorization_card_normalizer_le hJ hR hℓ2 h3 h5 hP₀E hP₀ne hP₀ℓ
    have h2 : Nat.card (Q₀ ⊔ P₀ : Subgroup G) ∣
        Nat.card (P ⊓ Subgroup.centralizer (P₀ : Set G) : Subgroup G) :=
      Subgroup.card_dvd_of_le (le_inf hQPP (sup_le hQ₀C hP₀C))
    rw [hc] at h2
    have h2' := (hℓ.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h2
    omega
  have hPne : P ≠ ⊥ := fun h => hP₀ne (le_bot_iff.mp (h ▸ hP₀P))
  obtain ⟨z, hzZ, hz⟩ := exists_mem_center_orderOf hPℓ hPne
  have hZK := s.center_le_K hℓ2 hℓp hℓK hP₀E hP₀card hPH hPℓ hPcard hP₀P
  have hzK : z ∈ s.K := hZK hzZ
  have hcycZ : IsCyclic (P ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) := by
    have hcyc : IsCyclic (P ⊓ s.K : Subgroup G) :=
      s.psl2Facts_K.cyclic ℓ hℓ hℓ2 hℓp _ inf_le_right (hPℓ.to_le inf_le_left)
    exact Subgroup.isCyclic_of_le (le_inf inf_le_left hZK)
  set M := Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.normalizer (P : Set G) with hM
  have hPC : P ≤ Subgroup.centralizer ({s.J} : Set G) := hPH
  have hJP : s.J ∈ Subgroup.normalizer (P : Set G) := by
    refine JT.mem_normalizer_of_conj_mem fun a ha => ?_
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hPC ha)
    rw [show s.J * a * s.J⁻¹ = a by rw [← h1, mul_inv_cancel_right]]
    exact ha
  have hJz : s.J ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (s.commute_J (s.K_le_H hzK)).symm
  have hJM : s.J ∈ M := ⟨hJz, hJP⟩
  have hPM : P ≤ M := fun x hx => ⟨Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hzZ.2 x hx), Subgroup.le_normalizer hx⟩
  have hM2 : (Nat.card M).factorization 2 = 1 := by
    have h1 := s.factorization_two_centralizer h4 hzK hz
    have h2 : (Nat.card M).factorization 2 ≤
        (Nat.card (Subgroup.centralizer ({z} : Set G))).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le inf_le_left) 2
    have h3' : 1 ≤ (Nat.card M).factorization 2 := by
      have h4' := Subgroup.orderOf_dvd_natCard M hJM
      rw [s.orderOf_J] at h4'
      exact (Nat.prime_two.dvd_iff_one_le_factorization Nat.card_pos.ne').mp h4'
    omega
  have hJ1 : (⟨s.J, hJM⟩ : M) ≠ 1 := fun h => s.J_ne_one (congrArg Subtype.val h)
  have hJ2 : (⟨s.J, hJM⟩ : M) * ⟨s.J, hJM⟩ = 1 := Subtype.ext s.J_mul_J
  obtain ⟨R, hJR⟩ := exists_sylow_mem_normalizer_of_two hℓ2 hM2 hJ1 hJ2
  have hPn : (P.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
  have hPMℓ : IsPGroup ℓ (P.subgroupOf M) := hPℓ.comap_subtype
  have hPR : P.subgroupOf M ≤ R := hPMℓ.le_sylow_of_normal R
  have hPR' : P ≤ (R : Subgroup M).map M.subtype := fun x hx =>
    ⟨⟨x, hPM hx⟩, hPR (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hJR' :
      s.J ∈ Subgroup.normalizer (((R : Subgroup M).map M.subtype : Subgroup G) : Set G) := by
    refine JT.mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨⟨s.J, hJM⟩ * y * (⟨s.J, hJM⟩ : M)⁻¹, (Subgroup.mem_normalizer_iff.mp hJR y).mp hy, rfl⟩
  have hPeq := s.eq_of_mem_normalizer_J hℓ2 hPH hPcard hP₀P hsyl (R.isPGroup'.map _) hPR' hJR'
  obtain ⟨RG, hPRG⟩ := hPℓ.exists_le_sylow
  have hXM : (RG : Subgroup G) ⊓ Subgroup.normalizer (P : Set G) ≤ M := by
    rintro x ⟨hxR, hxN⟩
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hxN⟩
    have hxz : x * z * x⁻¹ ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
      refine ⟨(Subgroup.mem_normalizer_iff.mp hxN z).mp hzZ.1,
        Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      have hy' : x⁻¹ * y * x ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) y).mp hy
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.mp hzZ.2 _ hy'
      calc y * (x * z * x⁻¹) = x * ((x⁻¹ * y * x) * z) * x⁻¹ := by group
        _ = x * (z * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
        _ = x * z * x⁻¹ * y := by group
    have hxzo : orderOf (x * z * x⁻¹) = ℓ := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
    have hzpow : Subgroup.zpowers (x * z * x⁻¹) = Subgroup.zpowers z :=
      eq_of_card_eq_of_le_cyclic hcycZ (Subgroup.zpowers_le.mpr hxz)
        (Subgroup.zpowers_le.mpr hzZ) (by rw [Nat.card_zpowers, Nat.card_zpowers, hxzo, hz])
    have hmem : x * z * x⁻¹ ∈ Subgroup.zpowers z := hzpow ▸ Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp RG.isPGroup') ⟨x, hxR⟩
    rw [Subgroup.orderOf_mk] at hk
    have hxz' := commute_of_prime_order hℓ hz hmem hk
    calc x * z = (x * z * x⁻¹) * x := by group
      _ = z * x := by rw [hxz']
  have hX : (RG : Subgroup G) ⊓ Subgroup.normalizer (P : Set G) ≤ P := by
    intro x hx
    have hXℓ : IsPGroup ℓ
        (((RG : Subgroup G) ⊓ Subgroup.normalizer (P : Set G)).subgroupOf M) :=
      (RG.isPGroup'.to_le inf_le_left).comap_subtype
    have hRX : (R : Subgroup M) ≤
        ((RG : Subgroup G) ⊓ Subgroup.normalizer (P : Set G)).subgroupOf M := by
      intro y hy
      have hyP : (y : G) ∈ (R : Subgroup M).map M.subtype := ⟨y, hy, rfl⟩
      rw [← hPeq] at hyP
      exact Subgroup.mem_subgroupOf.mpr ⟨hPRG hyP, Subgroup.le_normalizer hyP⟩
    have heq := R.is_maximal' hXℓ hRX
    have hxR : (⟨x, hXM hx⟩ : M) ∈ (R : Subgroup M) := by
      rw [← heq]
      exact Subgroup.mem_subgroupOf.mpr hx
    rw [hPeq]
    exact ⟨_, hxR, rfl⟩
  have hPRG' := eq_of_le_of_inf_normalizer_le RG.isPGroup' hPRG hX
  refine false_of_perfect_of_metacyclic s.perfect hℓ2 RG ?_ ?_
  · rw [← hPRG']
    exact s.not_isMulCommutative hℓ2 hℓp hℓK hP₀E hP₀ℓ hP₀ne hPH hPℓ hPcard hP₀P
  · rw [← hPRG']
    exact s.isMetacyclic hℓ2 hℓp hP₀E hP₀card hPH hPℓ hPcard hP₀P

end Std

end CFSG.Walter.W67

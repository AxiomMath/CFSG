module

public import CFSG.Quasithin.H13.A6S13820Aut3

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Aut20

variable {G : Type} [Group G]

theorem le_normalizer_commutator_left20 (A B : Subgroup G) :
    A ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have hfwd : ∀ a ∈ A, ∀ y ∈ ⁅A, B⁆, a * y * a⁻¹ ∈ ⁅A, B⁆ := by
    intro a ha y hy
    rw [Subgroup.commutator_def] at hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a', ha', b, hb, rfl⟩ := hx
      have e : a * ⁅a', b⁆ * a⁻¹ = ⁅a * a', b⁆ * ⁅a, b⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (A.mul_mem ha ha') hb)
        (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hb))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hfwd a ha y, fun hy => ?_⟩
  have := hfwd a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

theorem eq_one_of_two_odd20 {M : Type} [Monoid M] {x : M} {b m : ℕ} (h2 : x ^ 2 ^ b = 1)
    (hm : Odd m) (h : x ^ m = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ b) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hm)
  have h' := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h'
  exact h'

theorem mul_mem_of_odd20 {X : Subgroup G} {x q : G} (hx : x ∈ X)
    (hq : q ∈ Subgroup.normalizer (X : Set G)) {k : ℕ} (hq2 : q ^ 2 ^ k = 1) {m : ℕ}
    (hm : Odd m) (h : (x * q) ^ m = 1) : x * q ∈ X := by
  have h1 := mul_pow_mul_inv_mem20 hq hx m
  rw [h, one_mul] at h1
  have hqm : q ^ m ∈ X := by simpa using X.inv_mem h1
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hm)
  have hbez := Nat.gcd_eq_gcd_ab m (2 ^ k)
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  have e : q = (q ^ m) ^ Nat.gcdA m (2 ^ k) * (q ^ 2 ^ k) ^ Nat.gcdB m (2 ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast q (2 ^ k), ← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez,
      zpow_one]
  have hqX : q ∈ X := by
    rw [e, hq2, one_zpow, mul_one]
    exact X.zpow_mem hqm _
  exact X.mul_mem hx hqX

theorem pow12_20 : ∀ π : Perm (Fin 6), π 4 = 4 → π 5 = 5 → Perm.sign π = 1 → π ^ 12 = 1 := by
  decide +kernel

end Aut20

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pCoreOf_le_T_of_le_normalizer20 {Y : Subgroup G}
    (hY : T ≤ Subgroup.normalizer (Y : Set G)) : pCoreOf 2 Y ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow le_top
  have hsup : IsPGroup 2 ↥(T ⊔ pCoreOf 2 Y) :=
    hTs.2.1.to_sup_of_normal_right' (pCoreOf_isPGroup 2 Y)
      (hY.trans (normalizer_le_normalizer_pCoreOf 2 Y))
  exact le_sup_right.trans (Aut20.le_of_isSylowTwoOf_top20 hTs hsup le_sup_left)

theorem cube_eq_one20 {x : G} (hx : x ∈ S.X13820)
    (hodd : Odd (orderOf x)) : x ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := S.plusData_X13820
  have hxN := P.le_NV hx
  obtain ⟨h4, h5, hs⟩ := P.rho (x := ⟨x, hxN⟩) hx
  have h12 := Aut20.pow12_20 _ h4 h5 hs
  have hxo : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ orderOf x = 1 :=
    Subtype.ext (by simp [pow_orderOf_eq_one])
  have hdvd : orderOf (S.frame.ρ ⟨x, hxN⟩) ∣ 3 := by
    have h1 : orderOf (S.frame.ρ ⟨x, hxN⟩) ∣ orderOf x :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxo, map_one])
    have h2 : orderOf (S.frame.ρ ⟨x, hxN⟩) ∣ 4 * 3 := orderOf_dvd_of_pow_eq_one h12
    have hodd' : Odd (orderOf (S.frame.ρ ⟨x, hxN⟩)) := hodd.of_dvd_nat h1
    have hcop : Nat.Coprime (orderOf (S.frame.ρ ⟨x, hxN⟩)) 4 :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.2 hodd')
    exact hcop.dvd_of_dvd_mul_left h2
  have hρ3 : S.frame.ρ ⟨x ^ 3, Subgroup.pow_mem _ hxN 3⟩ = 1 := by
    have e : (⟨x ^ 3, Subgroup.pow_mem _ hxN 3⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨x, hxN⟩ ^ 3 := rfl
    rw [e, map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hx3 : x ^ 3 ∈ S.X13820 ⊓ Subgroup.centralizer (V : Set G) :=
    ⟨S.X13820.pow_mem hx 3, (S.rho_eq_one_iff _).1 hρ3⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨_, P.cent hx3⟩
  have hk' : (x ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine Aut20.eq_one_of_two_odd20 hk' hodd ?_
  rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]

theorem exists_odd_ne_one20 :
    ∃ x ∈ S.X13820, Odd (orderOf x) ∧ x ≠ 1 := by
  have P := S.plusData_X13820
  have hτ : (swap 0 1 * swap 1 2 : Perm (Fin 6)) ∈ S14.C3 := by decide
  obtain ⟨x, hxX, hρ⟩ := P.three _ hτ
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  have hym : (x ^ 4 ^ a) ^ m = 1 := by
    have h1 : (x ^ (4 ^ a)) ^ m = (x ^ (2 ^ a * m)) ^ (2 ^ a) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring
    rw [h1, ← hnm, pow_orderOf_eq_one, one_pow]
  refine ⟨((x ^ 4 ^ a : ↥(Subgroup.normalizer (V : Set G))) : G), ?_, ?_, ?_⟩
  · simpa using S.X13820.pow_mem hxX (4 ^ a)
  · rw [Subgroup.orderOf_coe]
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)
  · intro h1
    have h1' : x ^ 4 ^ a = 1 := Subtype.ext (by simpa using h1)
    have h3 := congrArg S.frame.ρ h1'
    rw [map_pow, hρ, pow_four_pow_of_cube (S14.c3_facts _ hτ).2.2.2, map_one] at h3
    exact absurd h3 (by decide)

theorem act20_X_eq_one20 {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hKH : K ≤ H) (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hLT : S.L1 ⊔ T ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) {t : G}
    (htX : ∀ x ∈ S.X13820, t * x * t⁻¹ * x ∈ pCoreOf 2 S.X13820)
    (htN : t ∈ Subgroup.normalizer (K : Set G)) {u : G} (hu : u ∈ T ⊓ K)
    (hα : Aut20.act20 K ⟨t, htN⟩ = MulAut.conj (Aut20.mk20 K ⟨u, hu.2⟩)) {x : G}
    (hx : x ∈ S.X13820) (hxN : x ∈ Subgroup.normalizer (K : Set G)) :
    Aut20.act20 K ⟨x, hxN⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := S.plusData_X13820
  have hXN : S.X13820 ≤ Subgroup.normalizer (K : Set G) :=
    (P.le_L1.trans (le_sup_left.trans hH.1.1)).trans hKn
  have hXT : S.X13820 ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    P.le_L1.trans (le_sup_left.trans hLT)
  have hO := S.pCoreOf_le_TK hH hKH hKn
  have hsyl := Aut20.isSylowTwoOf_Sb20 (S.isSylowTwoOf_TK hH hKH hKn)
  have hu' : Aut20.mk20 K ⟨u, hu.2⟩ ∈ ((T ⊓ K).subgroupOf K).map (Aut20.mk20 K) :=
    (Aut20.mem_map_mk20 hO _).2 hu
  have hodd : ∀ y ∈ S.X13820, Odd (orderOf y) →
      ∀ hyN : y ∈ Subgroup.normalizer (K : Set G), Aut20.act20 K ⟨y, hyN⟩ = 1 := by
    intro y hy hyodd hyN
    have hy3 := S.cube_eq_one20 hy hyodd
    have hoX := htX y hy
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 S.X13820 ⟨_, hoX⟩
    have hoN : t * y * t⁻¹ * y ∈ Subgroup.normalizer (K : Set G) := hXN (pCoreOf_le 2 _ hoX)
    have hξ : Aut20.act20 K ⟨y, hyN⟩ ^ 3 ^ 1 = 1 := by
      rw [pow_one, ← map_pow]
      have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
        Subtype.ext (by simpa using hy3)
      rw [this, map_one]
    have hω : Aut20.act20 K ⟨_, hoN⟩ ^ 2 ^ b = 1 := by
      rw [← map_pow]
      have : (⟨_, hoN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 2 ^ b = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hb)
      rw [this, map_one]
    have hξS := Aut20.map_act20_eq hO hyN (hXT hy)
    have hrel : MulAut.conj (Aut20.mk20 K ⟨u, hu.2⟩) * Aut20.act20 K ⟨y, hyN⟩ *
        (MulAut.conj (Aut20.mk20 K ⟨u, hu.2⟩))⁻¹ =
          Aut20.act20 K ⟨_, hoN⟩ * (Aut20.act20 K ⟨y, hyN⟩)⁻¹ := by
      rw [← hα, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact Aut20.eq_one_of_inv20 hsyl hξ hω hξS hu' hrel
  have hx' : x ∈ oTwoUpper S.X13820 := by
    have := hx
    rw [P.eq] at this
    exact this
  have hcl : oTwoUpper S.X13820 ≤ S.X13820 := oTwoUpper_le _
  clear hx
  revert hxN
  induction hx' using Subgroup.closure_induction with
  | mem y hy => exact hodd y hy.1 hy.2
  | one => intro h; exact (congrArg _ (Subtype.ext rfl : (⟨1, h⟩ : ↥(Subgroup.normalizer
      (K : Set G))) = 1)).trans (map_one _)
  | mul a b ha hb iha ihb =>
    intro h
    have haN := hXN (hcl ha)
    have hbN := hXN (hcl hb)
    have e : (⟨a * b, h⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨a, haN⟩ * ⟨b, hbN⟩ := rfl
    rw [e, map_mul, iha haN, ihb hbN, one_mul]
  | inv a ha iha =>
    intro h
    have haN := hXN (hcl ha)
    have e : (⟨a⁻¹, h⟩ : ↥(Subgroup.normalizer (K : Set G))) = (⟨a, haN⟩)⁻¹ := rfl
    rw [e, map_inv, iha haN, inv_one]

end Setting4

end CFSG.Quasithin.H13.A6

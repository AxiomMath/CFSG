module

import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.Extraspecial

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Q : Subgroup G} {z : G}

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma z_mem_inf_centralizer_and_card (hz : orderOf z = p)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z) :
    z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) ∧ Nat.card (Subgroup.zpowers z) = p :=
  ⟨hZ ▸ Subgroup.mem_zpowers z, by rw [Nat.card_zpowers, hz]⟩

omit [Finite G] in
private lemma center_subtype_eq_inf_centralizer (K : Subgroup G) :
    Subgroup.center ↥K = (K ⊓ Subgroup.centralizer (K : Set G)).subgroupOf K := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_center_iff]
  constructor
  · intro h
    refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact congrArg Subtype.val (h ⟨y, hy⟩)
  · rintro ⟨-, h⟩ y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h y y.2)

omit [Finite G] in
private lemma commutator_subtype_eq_subgroupOf (K : Subgroup G) :
    commutator ↥K = ⁅K, K⁆.subgroupOf K := by
  ext x
  constructor
  · intro hx
    exact Subgroup.mem_subgroupOf.mpr (by
      have h := Subgroup.mem_map_of_mem K.subtype hx
      rwa [Subgroup.map_subtype_commutator] at h)
  · intro hx
    have hx' : (x : G) ∈ (commutator ↥K).map K.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact Subgroup.mem_subgroupOf.mp hx
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
    exact (show y = x from Subtype.ext hxy) ▸ hy

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma commutator_pow_eq_one_of_mem_zpowers (hz : orderOf z = p)
    (hzC : z ∈ Subgroup.centralizer (Q : Set G))
    (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z) {x y : G} (hx : x ∈ Q) (hy : y ∈ Q) :
    ⁅x ^ p, y⁆ = 1 := by
  have hmem : ⁅x, y⁆ ∈ Subgroup.zpowers z :=
    hQQ (Subgroup.commutator_mem_commutator hx hy)
  have hcomm : Commute x ⁅x, y⁆ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hk]
    exact (show Commute x z from Subgroup.mem_centralizer_iff.mp hzC x hx).zpow_right k
  have hpow : ⁅x, y⁆ ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hk]
    have hzp : z ^ p = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    calc (z ^ k) ^ p = (z ^ k) ^ (p : ℤ) := (zpow_natCast _ _).symm
      _ = (z ^ (p : ℤ)) ^ k := zpow_comm z k (p : ℤ)
      _ = (z ^ p) ^ k := by rw [zpow_natCast]
      _ = 1 := by rw [hzp, one_zpow]
  calc ⁅x ^ p, y⁆ = ⁅x, y⁆ ^ p := (hcomm.commutatorElement_pow_left p).symm
    _ = 1 := hpow

omit [Finite G] in
private lemma commutator_eq_zpowers_of_not_commutative [Finite ↥(Subgroup.zpowers z)]
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hcomm : ¬ IsMulCommutative ↥Q) :
    (⁅Q, Q⁆ : Subgroup G) = Subgroup.zpowers z := by
  have hz_mem : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ Subgroup.mem_zpowers z
  have hzQ : z ∈ Q := hz_mem.1
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hQ'ne : (⁅Q, Q⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    exact hcomm ((Subgroup.commutator_self_eq_bot_iff).mp h)
  have hQ'card : Nat.card (⁅Q, Q⁆ : Subgroup G) = p := by
    have hdvd := Subgroup.card_dvd_of_le hQQ
    rw [hzcard] at hdvd
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
    · have hbot : (⁅Q, Q⁆ : Subgroup G) = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
      exact absurd hbot hQ'ne
    · exact hp
  exact Subgroup.eq_of_le_of_card_ge hQQ (by rw [hQ'card, hzcard])

omit [Finite G] in
private lemma center_eq_commutator_and_card_of_not_commutative [Finite ↥(Subgroup.zpowers z)]
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hcomm : ¬ IsMulCommutative ↥Q) :
    Subgroup.center ↥Q = commutator ↥Q ∧ Nat.card (Subgroup.center ↥Q) = p := by
  have hz_mem : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ Subgroup.mem_zpowers z
  have hzQ : z ∈ Q := hz_mem.1
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hQ'eq := commutator_eq_zpowers_of_not_commutative hz hQQ hZ hcomm
  constructor
  · rw [center_subtype_eq_inf_centralizer, hZ, commutator_subtype_eq_subgroupOf, hQ'eq]
  · rw [center_subtype_eq_inf_centralizer, hZ]
    calc Nat.card ((Subgroup.zpowers z).subgroupOf Q) = Nat.card (Subgroup.zpowers z) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hzQ)).toEquiv
      _ = p := hzcard

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma pow_mem_center_of_not_commutative
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z) :
    ∀ x : ↥Q, x ^ p ∈ Subgroup.center ↥Q := by
  have hz_mem : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ Subgroup.mem_zpowers z
  have hzC : z ∈ Subgroup.centralizer (Q : Set G) := hz_mem.2
  intro x
  have hmem : (x : G) ^ p ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := by
    refine ⟨pow_mem x.2 p, ?_⟩
    change (x : G) ^ p ∈ Subgroup.centralizer (Q : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : ⁅(x : G) ^ p, y⁆ = 1 := commutator_pow_eq_one_of_mem_zpowers hz hzC hQQ x.2 hy
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  rw [center_subtype_eq_inf_centralizer, hZ, Subgroup.mem_subgroupOf]
  exact hZ ▸ hmem

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma zmod_nsmul_zero_of_pow_mem_center
    (hcenter : Subgroup.center ↥Q = commutator ↥Q)
    (hpow : ∀ x : ↥Q, x ^ p ∈ Subgroup.center ↥Q) :
    ∀ v : Additive (Abelianization ↥Q), p • v = 0 := by
  intro v
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = v := ⟨Additive.toMul v, rfl⟩
  induction u using QuotientGroup.induction_on with
  | H x =>
    change Additive.ofMul ((Abelianization.of x) ^ p) = 0
    have hx : x ^ p ∈ commutator ↥Q := hcenter ▸ hpow x
    have hx1 : Abelianization.of (x ^ p) = 1 :=
      MonoidHom.mem_ker.mp (by rwa [Abelianization.ker_of])
    rw [← map_pow, hx1]
    rfl

omit [Finite G] in
private lemma exists_card_eq_pow_two_mul_add_one_of_not_commutative [Finite ↥Q]
    [Finite ↥(Subgroup.zpowers z)]
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hcomm : ¬ IsMulCommutative ↥Q) :
    ∃ n : ℕ, Nat.card Q = p ^ (2 * n + 1) := by
  obtain ⟨hcenter, hc⟩ := center_eq_commutator_and_card_of_not_commutative hz hQQ hZ hcomm
  have hpow := pow_mem_center_of_not_commutative hz hQQ hZ
  have hnsmul := zmod_nsmul_zero_of_pow_mem_center hcenter hpow
  let : Module (ZMod p) (Additive (Abelianization ↥Q)) := AddCommGroup.zmodModule hnsmul
  obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv (D := ↥Q) (r := p) hc
  obtain ⟨B, hBa, hBn, -⟩ := CFSG.OddSolvableUnitary.exists_commForm hcenter ε
  have : Finite (Additive (Abelianization ↥Q)) :=
    Finite.of_surjective (fun x : ↥Q => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have hFD : FiniteDimensional (ZMod p) (Additive (Abelianization ↥Q)) := Module.Finite.of_finite
  obtain ⟨a, ha⟩ := @LinearMap.BilinForm.IsAlt.even_finrank (ZMod p)
    (Additive (Abelianization ↥Q))
    (inferInstance : Field (ZMod p)) (inferInstance : AddCommGroup (Additive (Abelianization ↥Q)))
    (inferInstance : Module (ZMod p) (Additive (Abelianization ↥Q))) hFD B hBa hBn
  have hcardAb : Nat.card (Abelianization ↥Q) = p ^ (2 * a) := by
    have : Fintype (ZMod p) := Fintype.ofFinite _
    have : Fintype (Additive (Abelianization ↥Q)) := Fintype.ofFinite _
    have h1 : Nat.card (Additive (Abelianization ↥Q)) = p ^ (a + a) := by
      rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card, ha]
    rw [← two_mul] at h1
    exact h1
  have hcardQ : Nat.card ↥Q = p ^ (1 + 2 * a) := by
    rw [CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hcenter hc, hcardAb,
      pow_add, pow_one, mul_comm]
  refine ⟨a, ?_⟩
  rw [show 2 * a + 1 = 1 + 2 * a by omega]
  exact hcardQ

theorem exists_card_eq_pow_two_mul_add_one (hz : orderOf z = p)
    (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z) :
    ∃ n : ℕ, Nat.card Q = p ^ (2 * n + 1) := by
  have hz_mem : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ Subgroup.mem_zpowers z
  have hzQ : z ∈ Q := hz_mem.1
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  by_cases hcomm : IsMulCommutative ↥Q
  · have hle : Q ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr hcomm
    have hQeq : Q = Subgroup.zpowers z := by rw [← hZ, inf_eq_left.mpr hle]
    refine ⟨0, ?_⟩
    rw [hQeq, hzcard]
    norm_num
  · exact exists_card_eq_pow_two_mul_add_one_of_not_commutative hz hQQ hZ hcomm

@[instance_reducible]
private def conjAct (V K : Subgroup G) (hVK : V ≤ Subgroup.normalizer (K : Set G)) :
    MulDistribMulAction V K where
  smul v k := ⟨(v : G) * k * (v : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hVK v.2) k).mp k.2⟩
  one_smul k := Subtype.ext (by
    change ((1 : V) : G) * k * ((1 : V) : G)⁻¹ = k
    simp)
  mul_smul a b k := Subtype.ext (by
    change ((a : G) * b) * k * ((a : G) * b)⁻¹ = a * (b * k * (b : G)⁻¹) * (a : G)⁻¹
    group)
  smul_mul a x y := Subtype.ext (by
    change (a : G) * (x * y) * (a : G)⁻¹ = (a * x * (a : G)⁻¹) * (a * y * (a : G)⁻¹)
    group)
  smul_one a := Subtype.ext (by
    change (a : G) * 1 * (a : G)⁻¹ = 1
    group)

omit [Finite G] in
@[simp] private lemma conjAct_smul_coe {V K : Subgroup G}
    (hVK : V ≤ Subgroup.normalizer (K : Set G)) (v : V) (k : K) :
    letI := conjAct V K hVK
    (((v • k : K) : G)) = (v : G) * k * (v : G)⁻¹ := rfl

omit [Finite G] in
private lemma conj_eq_self_of_mem_zpowers (hzC : z ∈ Subgroup.centralizer (Q : Set G))
    {x w : G} (hx : x ∈ Q) (hw : w ∈ Subgroup.zpowers z) : x * w * x⁻¹ = w := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hk]
  have hxz : x * z * x⁻¹ = z := by
    have h := Subgroup.mem_centralizer_iff.mp hzC x hx
    rw [h, mul_inv_cancel_right]
  calc x * z ^ k * x⁻¹ = (x * z * x⁻¹) ^ k := (conj_zpow).symm
    _ = z ^ k := by rw [hxz]

private lemma card_modEq_card_inf_centralizer {K : Subgroup G} {u : G} {r : ℕ} [Fact r.Prime]
    (hu : orderOf u = r) (huK : u ∈ Subgroup.normalizer (K : Set G)) :
    Nat.card K ≡ Nat.card (K ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) [MOD r] := by
  classical
  have hle : Subgroup.zpowers u ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.zpowers_le).mpr huK
  let := conjAct (Subgroup.zpowers u) K hle
  have hp : IsPGroup r (Subgroup.zpowers u) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hu, pow_one])
  have hmod := hp.card_modEq_card_fixedPoints K
  have hsub : FixedPoints.subgroup (Subgroup.zpowers u) K =
      (K ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf K := by
    ext x
    rw [FixedPoints.mem_subgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      refine ⟨x.2, ?_⟩
      have h1 := congrArg (fun y : K => (y : G)) (hx ⟨u, Subgroup.mem_zpowers u⟩)
      change (u : G) * (x : G) * u⁻¹ = (x : G) at h1
      calc (x : G) * u = (u * (x : G) * u⁻¹) * u := by rw [h1]
        _ = u * (x : G) := by group
    · rintro ⟨-, hxu⟩
      intro g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
      apply Subtype.ext
      change (g : G) * (x : G) * (g : G)⁻¹ = (x : G)
      rw [← hk]
      have hcomm : Commute (u ^ k) (x : G) :=
        (show Commute u (x : G) from hxu.symm).zpow_left k
      rw [hcomm.eq, mul_inv_cancel_right]
  have hfixcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers u) K) =
      Nat.card (FixedPoints.subgroup (Subgroup.zpowers u) K) := rfl
  rw [hfixcard, hsub] at hmod
  refine hmod.trans ?_
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]

private lemma odd_le_six_cases {m : ℕ} (hm : Odd m) (h : m ≤ 6) :
    m = 1 ∨ m = 3 ∨ m = 5 := by
  obtain ⟨k, rfl⟩ := hm
  have hk : k ≤ 2 := by omega
  interval_cases k <;> simp

private lemma five_one_of_modEq_four {m c : ℕ} (hm : m = 1 ∨ m = 3 ∨ m = 5)
    (hc1 : 1 ≤ c) (hcm : c ≤ m) (hmod : m ≡ c [MOD 4]) (hne : c ≠ m) :
    m = 5 ∧ c = 1 := by
  rcases hm with rfl | rfl | rfl
  · omega
  · rw [Nat.ModEq] at hmod
    interval_cases c <;> omega
  · rw [Nat.ModEq] at hmod
    interval_cases c <;> omega

private lemma five_two_of_modEq_three {m c : ℕ} (hm : m = 1 ∨ m = 3 ∨ m = 5)
    (hc1 : 1 ≤ c) (hcm : c ≤ m) (hmod : m ≡ c [MOD 3]) (hne : c ≠ m) :
    m = 5 ∧ c = 2 := by
  rcases hm with rfl | rfl | rfl
  · omega
  · rw [Nat.ModEq] at hmod
    interval_cases c <;> omega
  · rw [Nat.ModEq] at hmod
    interval_cases c <;> omega

omit [Finite G] in
private lemma odd_index_cases_of_card_dvd {m : ℕ} (hQm : Nat.card Q = p ^ m)
    (hQ : Nat.card Q ∣ p ^ 6) (hm_odd : Odd m) : m = 1 ∨ m = 3 ∨ m = 5 := by
  apply odd_le_six_cases hm_odd
  have hdvd : p ^ m ∣ p ^ 6 := hQm ▸ hQ
  exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp hdvd

private lemma exists_card_eq_pow_odd_cases
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) :
    ∃ m : ℕ, Nat.card Q = p ^ m ∧ Odd m ∧ (m = 1 ∨ m = 3 ∨ m = 5) := by
  obtain ⟨n, hn⟩ := exists_card_eq_pow_two_mul_add_one hz hQQ hZ
  refine ⟨2 * n + 1, hn, ⟨n, rfl⟩, odd_index_cases_of_card_dvd hn hQ ⟨n, rfl⟩⟩

private lemma exists_card_eq_pow_of_le_of_mem_zpowers {P : Subgroup G} {m : ℕ}
    (hz : orderOf z = p) (hP : P ≤ Q) (hzP : z ∈ P) (hQm : Nat.card Q = p ^ m) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ m ∧ Nat.card P = p ^ c := by
  have hPdvd : Nat.card P ∣ p ^ m := by
    rw [← hQm]
    exact Subgroup.card_dvd_of_le hP
  obtain ⟨c, hc_le, hPcard⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hPdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hc_pos : 1 ≤ c := by
    have hp_le : p ≤ p ^ c := by
      rw [← hPcard]
      calc p = Nat.card (Subgroup.zpowers z) := by rw [Nat.card_zpowers, hz]
        _ ≤ Nat.card P := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr hzP)
    by_contra h
    have hc0 : c = 0 := by omega
    rw [hc0, pow_zero] at hp_le
    omega
  exact ⟨c, hc_pos, hc_le, hPcard⟩

omit [Finite G] in
private lemma card_eq_pow_four_of_card_mul_prime {K : Subgroup G}
    (h : Nat.card K * p = p ^ 5) : Nat.card K = p ^ 4 := by
  have h5 : p ^ 5 = p ^ 4 * p := by rw [show 5 = 4 + 1 by omega, pow_succ]
  rw [h5] at h
  exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma modEq_of_pow_modEq {k m c r : ℕ} [Fact r.Prime]
    (hk : orderOf (p : ZMod r) = k) (hkpos : 0 < k)
    (h : p ^ m ≡ p ^ c [MOD r]) : m ≡ c [MOD k] := by
  have hzmod : (p : ZMod r) ^ m = (p : ZMod r) ^ c := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ZMod.natCast_eq_natCast_iff]
    exact h
  have hf : IsOfFinOrder (p : ZMod r) := orderOf_pos_iff.mp (by rw [hk]; exact hkpos)
  have hcong := hf.pow_eq_pow_iff_modEq.mp hzmod
  rwa [hk] at hcong

omit [Finite G] in
private lemma mem_centralizer_of_inf_centralizer_eq {a : G}
    (h : Q ⊓ Subgroup.centralizer ({a} : Set G) = Q) :
    a ∈ Subgroup.centralizer (Q : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : x ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) := h.symm ▸ hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx').2

private lemma exists_card_inf_centralizer_eq_pow_and_modEq {s k m : ℕ} [Fact s.Prime] {f : G}
    (hz : orderOf z = p)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQm : Nat.card Q = p ^ m)
    (hk : orderOf (p : ZMod s) = k) (hkpos : 0 < k) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ m ∧
      Nat.card (Q ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = p ^ c ∧
      m ≡ c [MOD k] := by
  have hzCmem : z ∈ Q ⊓ Subgroup.centralizer ({f} : Set G) := by
    refine ⟨?_, ?_⟩
    · exact (hZ ▸ Subgroup.mem_zpowers z).1
    · change z ∈ Subgroup.centralizer ({f} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hfz.symm
  obtain ⟨c, hc_pos, hc_le, hCcard⟩ :=
    exists_card_eq_pow_of_le_of_mem_zpowers hz inf_le_left hzCmem hQm
  have hmodQ := card_modEq_card_inf_centralizer (K := Q) (u := f) hf hfQ
  have hmod : p ^ m ≡ p ^ c [MOD s] := by
    rw [hQm, hCcard] at hmodQ
    exact hmodQ
  exact ⟨c, hc_pos, hc_le, hCcard, modEq_of_pow_modEq hk hkpos hmod⟩

private lemma data_of_orderOf_eq_four {s : ℕ} [Fact s.Prime] {f : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hfC : f ∉ Subgroup.centralizer (Q : Set G)) :
    ∃ c : ℕ, c = 1 ∧ Nat.card (Q ⊓ Subgroup.centralizer ({f} : Set G) : Subgroup G) = p ^ c := by
  classical
  obtain ⟨m, hQm, -, hm_cases⟩ := exists_card_eq_pow_odd_cases hz hQQ hZ hQ
  obtain ⟨c, hc_pos, hc_le, hCcard, hcong⟩ :=
    exists_card_inf_centralizer_eq_pow_and_modEq (k := 4) hz hZ hQm hps (by norm_num) hf hfQ hfz
  have hne : c ≠ m := by
    intro hcm
    apply hfC
    apply mem_centralizer_of_inf_centralizer_eq
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hCcard, hcm, hQm]
  obtain ⟨-, hc1⟩ := five_one_of_modEq_four hm_cases hc_pos hc_le hcong hne
  exact ⟨c, hc1, hCcard⟩

theorem inf_centralizer_eq_zpowers_of_orderOf_eq_four {s : ℕ} [Fact s.Prime] {f : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hfC : f ∉ Subgroup.centralizer (Q : Set G)) :
    Q ⊓ Subgroup.centralizer {f} = Subgroup.zpowers z := by
  obtain ⟨c, hc1, hCcard⟩ := data_of_orderOf_eq_four hz hQQ hZ hQ hps hf hfQ hfz hfC
  have hz_mem : z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) := hZ ▸ Subgroup.mem_zpowers z
  have hzCmem : z ∈ Q ⊓ Subgroup.centralizer ({f} : Set G) := by
    refine ⟨hz_mem.1, ?_⟩
    change z ∈ Subgroup.centralizer ({f} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hfz.symm
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzCmem) ?_).symm
  rw [hCcard, hc1, hzcard]
  simp

private def commutatorHom {a : G} (hzC : z ∈ Subgroup.centralizer (Q : Set G))
    (hcomm : ∀ x ∈ Q, ⁅a, x⁆ ∈ Subgroup.zpowers z) : ↥Q →* Subgroup.zpowers z where
  toFun x := ⟨⁅a, (x : G)⁆, hcomm x x.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    change ⁅a, (x : G) * (y : G)⁆ = ⁅a, (x : G)⁆ * ⁅a, (y : G)⁆
    calc ⁅a, (x : G) * (y : G)⁆ =
          ⁅a, (x : G)⁆ * (x : G) * ⁅a, (y : G)⁆ * (x : G)⁻¹ :=
            commutatorElement_mul_right_eq_mul_conj a (x : G) (y : G)
      _ = ⁅a, (x : G)⁆ * ((x : G) * ⁅a, (y : G)⁆ * (x : G)⁻¹) := by group
      _ = ⁅a, (x : G)⁆ * ⁅a, (y : G)⁆ := by
            rw [conj_eq_self_of_mem_zpowers hzC x.2 (hcomm y y.2)]

omit [Finite G] in
private lemma ker_commutatorHom {a : G} (hzC : z ∈ Subgroup.centralizer (Q : Set G))
    (hcomm : ∀ x ∈ Q, ⁅a, x⁆ ∈ Subgroup.zpowers z) :
    (commutatorHom hzC hcomm).ker = (Q ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf Q := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 : ⁅a, (x : G)⁆ = 1 := by
      have hval := congrArg (fun y : Subgroup.zpowers z => (y : G)) h
      change ⁅a, (x : G)⁆ = 1 at hval
      exact hval
    exact ⟨x.2, (commutatorElement_eq_one_iff_mul_comm.mp h1).symm⟩
  · rintro ⟨-, hx⟩
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr hx.symm

omit [Finite G] in
private lemma range_commutatorHom_ne_bot {a : G} (hzC : z ∈ Subgroup.centralizer (Q : Set G))
    (hcomm : ∀ x ∈ Q, ⁅a, x⁆ ∈ Subgroup.zpowers z)
    (haC : a ∉ Subgroup.centralizer (Q : Set G)) :
    (commutatorHom hzC hcomm).range ≠ ⊥ := by
  intro hbot
  have h1 : ∀ x : ↥Q, commutatorHom hzC hcomm x = 1 := by
    intro x
    have hx : commutatorHom hzC hcomm x ∈ (commutatorHom hzC hcomm).range :=
      MonoidHom.mem_range.mpr ⟨x, rfl⟩
    rwa [hbot] at hx
  rw [Subgroup.mem_centralizer_iff] at haC
  push Not at haC
  obtain ⟨x, hxQ, hne⟩ := haC
  have h2 : ⁅a, x⁆ = 1 := by
    have hval := congrArg (fun y : Subgroup.zpowers z => (y : G)) (h1 ⟨x, hxQ⟩)
    change ⁅a, x⁆ = 1 at hval
    exact hval
  exact hne (commutatorElement_eq_one_iff_mul_comm.mp h2).symm

omit [Finite G] in
private lemma card_inf_centralizer_mul_prime_of_comm {a : G}
    (hz : orderOf z = p) (hzC : z ∈ Subgroup.centralizer (Q : Set G))
    (hcomm : ∀ x ∈ Q, ⁅a, x⁆ ∈ Subgroup.zpowers z)
    (haC : a ∉ Subgroup.centralizer (Q : Set G)) :
    Nat.card (Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p = Nat.card Q := by
  classical
  have hker := ker_commutatorHom hzC hcomm
  have hrange := range_commutatorHom_ne_bot hzC hcomm haC
  let φ := commutatorHom hzC hcomm
  have : Fact (Nat.card (Subgroup.zpowers z)).Prime :=
    ⟨by rw [Nat.card_zpowers, hz]; exact Fact.out⟩
  have htop : φ.range = ⊤ := (φ.range.eq_bot_or_eq_top_of_prime_card).resolve_left hrange
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp htop
  have hcard := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, Nat.card_zpowers, hz] at hcard
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
  exact hcard

omit [Finite G] in
private lemma mem_normalizer_inf_centralizer {K : Subgroup G} {a u : G}
    (huK : u ∈ Subgroup.normalizer (K : Set G)) (hua : u * a = a * u) :
    u ∈ Subgroup.normalizer (K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) := by
  have hle : Subgroup.zpowers u ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro g hg x hx
    refine ⟨?_, ?_⟩
    · exact (Subgroup.le_normalizer_iff.mp ((Subgroup.zpowers_le).mpr huK)) g hg x hx.1
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hgcomm : Commute g a := by
        rw [← hk]
        exact (show Commute u a from hua).zpow_left k
      have hxcomm : Commute x a := by
        exact Subgroup.mem_centralizer_singleton_iff.mp hx.2
      change g * x * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact ((hgcomm.mul_left hxcomm).mul_left hgcomm.inv_left).eq
  exact (Subgroup.zpowers_le).mp hle

private lemma orderOf_eq_three_data {r : ℕ} [Fact r.Prime] {u : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hpr : orderOf (p : ZMod r) = 3) (hu : orderOf u = r)
    (huQ : u ∈ Subgroup.normalizer (Q : Set G)) (huz : u * z = z * u) :
    (Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = Nat.card Q) ∨
      (Nat.card Q = p ^ 5 ∧
        Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = p ^ 2) := by
  classical
  obtain ⟨m, hQm, -, hm_cases⟩ := exists_card_eq_pow_odd_cases hz hQQ hZ hQ
  obtain ⟨c, hc_pos, hc_le, hPcard, hcong⟩ :=
    exists_card_inf_centralizer_eq_pow_and_modEq (k := 3) hz hZ hQm hpr (by norm_num) hu huQ huz
  by_cases hcm : c = m
  · left
    rw [hPcard, hcm, hQm]
  · right
    obtain ⟨hm5, hc2⟩ := five_two_of_modEq_three hm_cases hc_pos hc_le hcong hcm
    exact ⟨by rw [hQm, hm5], by rw [hPcard, hc2]⟩

private lemma exists_centralizing_element_of_card_eq_prime_sq {u : G}
    (hz : orderOf z = p)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ5 : Nat.card Q = p ^ 5)
    (hPcard2 : Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = p ^ 2) :
    ∃ a : G, a ∈ Q ⊓ Subgroup.centralizer ({u} : Set G) ∧ a ∉ Subgroup.zpowers z ∧
      a ∉ Subgroup.centralizer (Q : Set G) ∧
      (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤
        Q ⊓ Subgroup.centralizer ({a} : Set G) := by
  classical
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  set P : Subgroup G := Q ⊓ Subgroup.centralizer ({u} : Set G) with hPdef
  have hPcard2P : Nat.card P = p ^ 2 := by simpa [hPdef] using hPcard2
  have hex : ∃ a ∈ P, a ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    have hle : P ≤ Subgroup.zpowers z := fun a ha => h a ha
    have hcardle : Nat.card P ≤ Nat.card (Subgroup.zpowers z) := Subgroup.card_le_of_le hle
    rw [hPcard2P, hzcard] at hcardle
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h21 : 2 ≤ 1 := (Nat.pow_le_pow_iff_right hp2).mp (by simpa using hcardle)
    omega
  obtain ⟨a, haP, haZ⟩ := hex
  have haP' : a ∈ Q ⊓ Subgroup.centralizer ({u} : Set G) := hPdef ▸ haP
  have haQ : a ∈ Q := (Subgroup.mem_inf.mp haP').1
  have haC : a ∉ Subgroup.centralizer (Q : Set G) := by
    intro h
    exact haZ (hZ ▸ ⟨haQ, h⟩)
  have hQp : IsPGroup p ↥Q := IsPGroup.of_card hQ5
  have : IsPGroup p ↥P := hQp.to_le (by exact inf_le_left : P ≤ Q)
  have : IsMulCommutative ↥P := IsPGroup.isMulCommutative_of_card_eq_prime_sq hPcard2P
  have hleCa : P ≤ Q ⊓ Subgroup.centralizer ({a} : Set G) := by
    refine le_inf inf_le_left ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm' ⟨x, hx⟩ ⟨a, haP⟩)
  exact ⟨a, haP', haZ, haC, hleCa⟩

private lemma false_of_centralizing_of_card_eq_prime_sq {r : ℕ} [Fact r.Prime] {u a : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hzC : z ∈ Subgroup.centralizer (Q : Set G))
    (hpr : orderOf (p : ZMod r) = 3) (hu : orderOf u = r)
    (huQ : u ∈ Subgroup.normalizer (Q : Set G))
    (hQ5 : Nat.card Q = p ^ 5)
    (haQ : a ∈ Q) (haC : a ∉ Subgroup.centralizer (Q : Set G))
    (hua : u * a = a * u)
    (hPcard2 : Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = p ^ 2)
    (hPle : (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) ≤
      Q ⊓ Subgroup.centralizer ({a} : Set G)) : False := by
  classical
  have hcomm_a : ∀ x ∈ Q, ⁅a, x⁆ ∈ Subgroup.zpowers z := fun x hx =>
    hQQ (Subgroup.commutator_mem_commutator haQ hx)
  have hKa := card_inf_centralizer_mul_prime_of_comm hz hzC hcomm_a haC
  have hKa' : Nat.card (Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) * p = p ^ 5 := by
    rw [hQ5] at hKa
    exact hKa
  have hKcard : Nat.card (Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) = p ^ 4 :=
    card_eq_pow_four_of_card_mul_prime hKa'
  have huK : u ∈ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_centralizer (K := Q) huQ hua
  have hmodK := card_modEq_card_inf_centralizer (K := Q ⊓ Subgroup.centralizer ({a} : Set G))
    (u := u) hu huK
  have hKinf : (Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ⊓
      Subgroup.centralizer ({u} : Set G) = Q ⊓ Subgroup.centralizer ({u} : Set G) := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxK, hxu⟩ := Subgroup.mem_inf.mp hx
      exact ⟨(Subgroup.mem_inf.mp hxK).1, hxu⟩
    · intro x hx
      exact ⟨hPle hx, (Subgroup.mem_inf.mp hx).2⟩
  have hmod4 : p ^ 4 ≡ p ^ 2 [MOD r] := by
    rw [hKcard, hKinf, hPcard2] at hmodK
    exact hmodK
  have hcong42 : 4 ≡ 2 [MOD 3] := modEq_of_pow_modEq hpr (by norm_num) hmod4
  rw [Nat.ModEq] at hcong42
  norm_num at hcong42

private lemma bad_case_of_orderOf_eq_three {r : ℕ} [Fact r.Prime] {u : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hpr : orderOf (p : ZMod r) = 3) (hu : orderOf u = r)
    (huQ : u ∈ Subgroup.normalizer (Q : Set G))
    (hQ5 : Nat.card Q = p ^ 5)
    (hPcard2 : Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) = p ^ 2) :
    u ∈ Subgroup.centralizer (Q : Set G) := by
  classical
  have hzC : z ∈ Subgroup.centralizer (Q : Set G) :=
    (z_mem_inf_centralizer_and_card hz hZ).1.2
  obtain ⟨a, haP, _, haC, hPle⟩ :=
    exists_centralizing_element_of_card_eq_prime_sq hz hZ hQ5 hPcard2
  have haQ : a ∈ Q := (Subgroup.mem_inf.mp haP).1
  have hau : a * u = u * a :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp haP).2
  exact (false_of_centralizing_of_card_eq_prime_sq hz hQQ hzC hpr hu huQ hQ5 haQ haC
    hau.symm hPcard2 hPle).elim

theorem mem_centralizer_of_orderOf_eq_three {r : ℕ} [Fact r.Prime] {u : G} (hz : orderOf z = p)
    (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hpr : orderOf (p : ZMod r) = 3) (hu : orderOf u = r)
    (huQ : u ∈ Subgroup.normalizer (Q : Set G)) (huz : u * z = z * u) :
    u ∈ Subgroup.centralizer (Q : Set G) := by
  rcases orderOf_eq_three_data hz hQQ hZ hQ hpr hu huQ huz with hP | ⟨hQ5, hPcard2⟩
  · have hPQ : Q ⊓ Subgroup.centralizer ({u} : Set G) = Q := by
      refine Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hP.symm)
    exact mem_centralizer_of_inf_centralizer_eq hPQ
  · exact bad_case_of_orderOf_eq_three hz hQQ hZ hpr hu huQ hQ5 hPcard2

omit [Finite G] in
private lemma conj_eq_self_of_mem_zpowers_of_commute {x w : G}
    (hxz : x * z = z * x) (hw : w ∈ Subgroup.zpowers z) : x * w * x⁻¹ = w := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  rw [← hk]
  have hconj : x * z * x⁻¹ = z := by rw [hxz, mul_inv_cancel_right]
  calc x * z ^ k * x⁻¹ = (x * z * x⁻¹) ^ k := (conj_zpow).symm
    _ = z ^ k := by rw [hconj]

private def Xsubgroup (Q : Subgroup G) (z y : G)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z) : Subgroup G where
  carrier := {x | x ∈ Q ∧ ⁅x, y⁆ ∈ Subgroup.zpowers z}
  one_mem' := ⟨Q.one_mem, by simp⟩
  mul_mem' := by
    intro x1 x2 hx1 hx2
    have hzC : z ∈ Subgroup.centralizer (Q : Set G) := (hZ ▸ Subgroup.mem_zpowers z).2
    refine ⟨mul_mem hx1.1 hx2.1, ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul,
      conj_eq_self_of_mem_zpowers hzC hx1.1 hx2.2]
    exact (Subgroup.zpowers z).mul_mem hx2.2 hx1.2
  inv_mem' := by
    intro x hx
    have hzC : z ∈ Subgroup.centralizer (Q : Set G) := (hZ ▸ Subgroup.mem_zpowers z).2
    refine ⟨inv_mem hx.1, ?_⟩
    have hyx : ⁅y, x⁆ ∈ Subgroup.zpowers z := by
      have h := (Subgroup.zpowers z).inv_mem hx.2
      rwa [commutatorElement_inv] at h
    have h : ⁅x⁻¹, y⁆ = ⁅y, x⁆ := by
      calc ⁅x⁻¹, y⁆ = x⁻¹ * ⁅y, x⁆ * x := commutatorElement_inv_left x y
        _ = ⁅y, x⁆ := by
              simpa using conj_eq_self_of_mem_zpowers hzC (inv_mem hx.1) hyx
    rwa [h]

omit [Finite G] in
private lemma Xsubgroup_le (Q : Subgroup G) (z y : G)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z) :
    Xsubgroup Q z y hZ ≤ Q := fun _ hx => hx.1

omit [Finite G] in
private lemma conj_mem_Xsubgroup {Q : Subgroup G} {z y g x : G}
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set G))
    (hgz : g * z = z * g) (hgy : g * y = y * g)
    (hx : x ∈ Xsubgroup Q z y hZ) : g * x * g⁻¹ ∈ Xsubgroup Q z y hZ := by
  have hzC : z ∈ Subgroup.centralizer (Q : Set G) := (hZ ▸ Subgroup.mem_zpowers z).2
  refine ⟨?_, ?_⟩
  · have hg'Q : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hgQ
    simpa using (Subgroup.mem_set_normalizer_iff''.mp hg'Q x).mp hx.1
  · have hgy' : g * y * g⁻¹ = y := by
      have hcomm : Commute g y := hgy
      calc g * y * g⁻¹ = (y * g) * g⁻¹ := by rw [hcomm.eq]
        _ = y := by group
    have hconj : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ :=
      (conjugate_commutatorElement (g₁ := x) (g₂ := y) (g₃ := g)).symm
    rw [hgy'] at hconj
    rw [hconj, conj_eq_self_of_mem_zpowers_of_commute hgz hx.2]
    exact hx.2

omit [Finite G] in
private lemma mem_normalizer_Xsubgroup {Q : Subgroup G} {z y f : G}
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hyf : y * f = f * y) :
    f ∈ Subgroup.normalizer (Xsubgroup Q z y hZ : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff'']
  intro x
  constructor
  · intro hx
    have hf'Q : f⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hfQ
    have hf'z : f⁻¹ * z = z * f⁻¹ := (show Commute f z from hfz).inv_left.eq
    have hf'y : f⁻¹ * y = y * f⁻¹ := (show Commute f y from hyf.symm).inv_left.eq
    simpa using conj_mem_Xsubgroup hZ hf'Q hf'z hf'y hx
  · intro hx
    have h := conj_mem_Xsubgroup hZ hfQ hfz hyf.symm hx
    have hx' : f * (f⁻¹ * x * f) * f⁻¹ = x := by group
    rwa [hx'] at h

omit [Finite G] in
private lemma quotientAction_conjAct {y : G}
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) (hyz : y * z = z * y) :
    letI : MulDistribMulAction (Subgroup.zpowers y) ↥Q :=
      conjAct (Subgroup.zpowers y) Q ((Subgroup.zpowers_le).mpr hyQ)
    MulAction.QuotientAction (Subgroup.zpowers y) ((Subgroup.zpowers z).subgroupOf Q) := by
  let : MulDistribMulAction (Subgroup.zpowers y) ↥Q :=
    conjAct (Subgroup.zpowers y) Q ((Subgroup.zpowers_le).mpr hyQ)
  refine ⟨fun b {a a'} haa' => ?_⟩
  have hbz : (b : G) * z = z * (b : G) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk]
    exact (show Commute y z from hyz).zpow_left k |>.eq
  rw [Subgroup.mem_subgroupOf] at haa' ⊢
  have hval : (((b • a)⁻¹ * (b • a') : ↥Q) : G) =
      (b : G) * ((a⁻¹ * a' : ↥Q) : G) * (b : G)⁻¹ := by
    simp [Subgroup.coe_mul, conjAct_smul_coe, mul_assoc]
  rw [hval]
  rw [conj_eq_self_of_mem_zpowers_of_commute hbz haa']
  exact haa'

omit [Finite G] in
private lemma z_mem_Xsubgroup {y : G}
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hyz : y * z = z * y) : z ∈ Xsubgroup Q z y hZ := by
  refine ⟨(hZ ▸ Subgroup.mem_zpowers z).1, ?_⟩
  have h1 : ⁅z, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hyz.symm
  rw [h1]
  exact (Subgroup.zpowers z).one_mem

omit [Finite G] in
private lemma Xsubgroup_inf_centralizer_eq_zpowers {f y : G}
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hyz : y * z = z * y) (hfz : f * z = z * f)
    (hCf : Q ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z) :
    Xsubgroup Q z y hZ ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z := by
  have hzCf : z ∈ Subgroup.centralizer ({f} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hfz.symm
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxX, hxf⟩ := Subgroup.mem_inf.mp hx
    exact hCf ▸ ⟨hxX.1, hxf⟩
  · intro x hx
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.zpowers_le.mpr (z_mem_Xsubgroup hZ hyz) hx,
        Subgroup.zpowers_le.mpr hzCf hx⟩

omit [Finite G] in
private lemma isPGroup_zpowers_of_pow_eq_one {y : G} (hy : ∃ k : ℕ, y ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers y) := by
  obtain ⟨k, hk⟩ := hy
  have hdvd : orderOf y ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

omit [Fact (Nat.Prime p)] in
private lemma eq_five_of_card_eq_pow_of_modEq_one {j : ℕ} {X : Subgroup G}
    (hz : orderOf z = p) (hzX : Subgroup.zpowers z ≤ X)
    (hXcard : Nat.card X = p ^ j) (hj_le : j ≤ 5) (hj1 : j ≡ 1 [MOD 4])
    (hXne : X ≠ Subgroup.zpowers z) : j = 5 := by
  have hj_cases : j = 1 ∨ j = 5 := by
    rw [Nat.ModEq] at hj1
    interval_cases j <;> omega
  rcases hj_cases with rfl | rfl
  · exfalso
    apply hXne
    have hXp : Nat.card X = p := by rw [hXcard]; norm_num
    refine (Subgroup.eq_of_le_of_card_ge hzX ?_).symm
    rw [hXp, Nat.card_zpowers, hz]
  · rfl

private lemma exists_card_Xsubgroup_eq_pow_and_modEq_one {s : ℕ} [Fact s.Prime] {f y : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hfC : f ∉ Subgroup.centralizer (Q : Set G))
    (hyz : y * z = z * y) (hyf : y * f = f * y) (hQ5 : Nat.card Q = p ^ 5) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 5 ∧ Nat.card (Xsubgroup Q z y hZ) = p ^ j ∧
      j ≡ 1 [MOD 4] := by
  classical
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hCf : Q ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z :=
    inf_centralizer_eq_zpowers_of_orderOf_eq_four hz hQQ hZ hQ hps hf hfQ hfz hfC
  let X := Xsubgroup Q z y hZ
  have hXle : X ≤ Q := Xsubgroup_le Q z y hZ
  have hXinf : X ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z :=
    Xsubgroup_inf_centralizer_eq_zpowers hZ hyz hfz hCf
  have hfXnorm : f ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_Xsubgroup hZ hfQ hfz hyf
  have hmodX := card_modEq_card_inf_centralizer (K := X) (u := f) hf hfXnorm
  have hmodXp : Nat.card X ≡ p [MOD s] := by
    rw [hXinf, hzcard] at hmodX
    exact hmodX
  have hXdvd : Nat.card X ∣ p ^ 5 := by
    rw [← hQ5]
    exact Subgroup.card_dvd_of_le hXle
  obtain ⟨j, hj_le, hXcard⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hXdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hj_pos : 1 ≤ j := by
    have hp_le : p ≤ p ^ j := by
      rw [← hXcard]
      calc p = Nat.card (Subgroup.zpowers z) := hzcard.symm
        _ ≤ Nat.card X := Subgroup.card_le_of_le (Subgroup.zpowers_le.mpr (z_mem_Xsubgroup hZ hyz))
    by_contra h
    have hj0 : j = 0 := by omega
    rw [hj0, pow_zero] at hp_le
    omega
  have hcongj : j ≡ 1 [MOD 4] := by
    have hmodXj : p ^ j ≡ p ^ 1 [MOD s] := by
      rw [hXcard] at hmodXp
      simpa using hmodXp
    exact modEq_of_pow_modEq hps (by norm_num) hmodXj
  exact ⟨j, hj_pos, hj_le, hXcard, hcongj⟩

private lemma exists_fixedPoint_ne_one_quotient {y : G}
    (hz : orderOf z = p)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hyz : y * z = z * y) (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hyp : IsPGroup p (Subgroup.zpowers y)) (hQ5 : Nat.card Q = p ^ 5) :
    letI : MulDistribMulAction (Subgroup.zpowers y) ↥Q :=
      conjAct (Subgroup.zpowers y) Q ((Subgroup.zpowers_le).mpr hyQ)
    letI : MulAction.QuotientAction (Subgroup.zpowers y)
        ((Subgroup.zpowers z).subgroupOf Q) := quotientAction_conjAct hyQ hyz
    ∃ q : MulAction.fixedPoints (Subgroup.zpowers y)
      (↥Q ⧸ (Subgroup.zpowers z).subgroupOf Q),
      (q : ↥Q ⧸ (Subgroup.zpowers z).subgroupOf Q) ≠ QuotientGroup.mk 1 := by
  let : MulDistribMulAction (Subgroup.zpowers y) ↥Q :=
    conjAct (Subgroup.zpowers y) Q ((Subgroup.zpowers_le).mpr hyQ)
  let : MulAction.QuotientAction (Subgroup.zpowers y)
      ((Subgroup.zpowers z).subgroupOf Q) := quotientAction_conjAct hyQ hyz
  obtain ⟨⟨hzQ, -⟩, hzcard⟩ := z_mem_inf_centralizer_and_card hz hZ
  let L : Subgroup ↥Q := (Subgroup.zpowers z).subgroupOf Q
  have : L.Normal := by
    rw [show L = Subgroup.center ↥Q by rw [center_subtype_eq_inf_centralizer, hZ]]
    infer_instance
  have : Finite (↥Q ⧸ L) :=
    Finite.of_surjective (QuotientGroup.mk' L) (QuotientGroup.mk'_surjective L)
  have hLcard : Nat.card L = p := by
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hzQ)).toEquiv, hzcard]
  have hVcard : Nat.card (↥Q ⧸ L) = p ^ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup L
    rw [hQ5, hLcard] at h1
    rw [show p ^ 5 = p ^ 4 * p by rw [show 5 = 4 + 1 by omega, pow_succ]] at h1
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h1.symm
  have hmod := hyp.card_modEq_card_fixedPoints (↥Q ⧸ L)
  have hVdvd : p ∣ Nat.card (↥Q ⧸ L) := by rw [hVcard]; exact dvd_pow_self p (by norm_num)
  have hfixdvd : p ∣ Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) (↥Q ⧸ L)) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hVdvd))
  have hone : (1 : ↥Q ⧸ L) ∈ MulAction.fixedPoints (Subgroup.zpowers y) (↥Q ⧸ L) := by
    rw [MulAction.mem_fixedPoints]
    intro b
    rw [show (1 : ↥Q ⧸ L) = QuotientGroup.mk (1 : ↥Q) from (QuotientGroup.mk_one L).symm,
      MulAction.Quotient.smul_mk]
    simp
  have hfixpos : 0 < Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) (↥Q ⧸ L)) :=
    Finite.card_pos_iff.mpr ⟨⟨1, hone⟩⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hfixgt1 : 1 < Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) (↥Q ⧸ L)) := by
    have hge : p ≤ Nat.card (MulAction.fixedPoints (Subgroup.zpowers y) (↥Q ⧸ L)) :=
      Nat.le_of_dvd hfixpos hfixdvd
    omega
  have : Nontrivial (MulAction.fixedPoints (Subgroup.zpowers y) (↥Q ⧸ L)) :=
    Finite.one_lt_card_iff_nontrivial.mp hfixgt1
  obtain ⟨q, hqne⟩ :=
    exists_ne (⟨1, hone⟩ : MulAction.fixedPoints (Subgroup.zpowers y) (↥Q ⧸ L))
  exact ⟨q, fun hq => hqne (Subtype.ext (by simpa [QuotientGroup.mk_one] using hq))⟩

omit [Finite G] in
private lemma exists_mem_Xsubgroup_of_fixedPoint_ne_one {y : G}
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) (hyz : y * z = z * y) :
    letI : MulDistribMulAction (Subgroup.zpowers y) ↥Q :=
      conjAct (Subgroup.zpowers y) Q ((Subgroup.zpowers_le).mpr hyQ)
    letI : MulAction.QuotientAction (Subgroup.zpowers y)
        ((Subgroup.zpowers z).subgroupOf Q) := quotientAction_conjAct hyQ hyz
    (∃ q : MulAction.fixedPoints (Subgroup.zpowers y)
      (↥Q ⧸ (Subgroup.zpowers z).subgroupOf Q),
      (q : ↥Q ⧸ (Subgroup.zpowers z).subgroupOf Q) ≠ QuotientGroup.mk 1) →
    ∃ x : G, x ∈ Xsubgroup Q z y hZ ∧ x ∉ Subgroup.zpowers z := by
  let : MulDistribMulAction (Subgroup.zpowers y) ↥Q :=
    conjAct (Subgroup.zpowers y) Q ((Subgroup.zpowers_le).mpr hyQ)
  let : MulAction.QuotientAction (Subgroup.zpowers y)
      ((Subgroup.zpowers z).subgroupOf Q) := quotientAction_conjAct hyQ hyz
  rintro ⟨q, hqne⟩
  let L : Subgroup ↥Q := (Subgroup.zpowers z).subgroupOf Q
  have hLcenter : L = Subgroup.center ↥Q := by
    rw [center_subtype_eq_inf_centralizer, hZ]
  have : L.Normal := by rw [hLcenter]; infer_instance
  let x : ↥Q := Quotient.out q.1
  have hxq : QuotientGroup.mk x = q.1 := Quotient.out_eq' q.1
  have hxL : x ∉ L := by
    intro hx
    apply hqne
    rw [← hxq, (QuotientGroup.eq_one_iff x).mpr hx]
    rfl
  have hyfix : (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) • q.1 = q.1 := q.2 _
  have hb : QuotientGroup.mk
      ((⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) • x) = q.1 := by
    rw [← MulAction.Quotient.smul_mk L]
    rw [hxq]
    exact hyfix
  have hbq : QuotientGroup.mk ((⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) • x) =
      QuotientGroup.mk x := hb.trans hxq.symm
  have hdiv : ((⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) • x) / x ∈ L :=
    QuotientGroup.eq_iff_div_mem.mp hbq
  have hdivG : ⁅y, (x : G)⁆ ∈ Subgroup.zpowers z := by
    have h := Subgroup.mem_subgroupOf.mp hdiv
    have hval : ((((⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) • x) / x : ↥Q) : G) =
        ⁅y, (x : G)⁆ := by
      simp [conjAct_smul_coe, div_eq_mul_inv, commutatorElement_def]
    rw [hval] at h
    exact h
  have hxcomm : ⁅(x : G), y⁆ ∈ Subgroup.zpowers z := by
    have h := (Subgroup.zpowers z).inv_mem hdivG
    rwa [commutatorElement_inv] at h
  exact ⟨(x : G), ⟨x.2, hxcomm⟩, fun h => hxL (Subgroup.mem_subgroupOf.mpr h)⟩

private lemma exists_mem_Xsubgroup_not_mem_zpowers {y : G}
    (hz : orderOf z = p)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hyz : y * z = z * y)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hyp : IsPGroup p (Subgroup.zpowers y))
    (hQ5 : Nat.card Q = p ^ 5) :
    ∃ x : G, x ∈ Xsubgroup Q z y hZ ∧ x ∉ Subgroup.zpowers z := by
  obtain ⟨q, hq⟩ := exists_fixedPoint_ne_one_quotient hz hZ hyz hyQ hyp hQ5
  exact exists_mem_Xsubgroup_of_fixedPoint_ne_one hZ hyQ hyz ⟨q, hq⟩

private lemma card_eq_pow_five_of_orderOf_eq_four {s : ℕ} [Fact s.Prime] {f : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hfC : f ∉ Subgroup.centralizer (Q : Set G)) :
    Nat.card Q = p ^ 5 := by
  classical
  obtain ⟨m, hQm, -, hm_cases⟩ := exists_card_eq_pow_odd_cases hz hQQ hZ hQ
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hz]
  have hCf : Q ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z :=
    inf_centralizer_eq_zpowers_of_orderOf_eq_four hz hQQ hZ hQ hps hf hfQ hfz hfC
  have hmodQ := card_modEq_card_inf_centralizer (K := Q) (u := f) hf hfQ
  have hmod : p ^ m ≡ p ^ 1 [MOD s] := by
    rw [hQm, hCf, hzcard] at hmodQ
    simpa using hmodQ
  have hcong : m ≡ 1 [MOD 4] := modEq_of_pow_modEq hps (by norm_num) hmod
  have hm5 : m = 5 := by
    rcases hm_cases with h1 | h3 | h5
    · exfalso
      apply hfC
      have hQ1 : Nat.card Q = p := by rw [hQm, h1]; norm_num
      have hCfQ : Q ⊓ Subgroup.centralizer ({f} : Set G) = Q := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hCf, hzcard, hQ1]
      exact mem_centralizer_of_inf_centralizer_eq hCfQ
    · exfalso
      rw [h3] at hcong
      rw [Nat.ModEq] at hcong
      norm_num at hcong
    · exact h5
  rw [hQm, hm5]

private lemma X_eq_Q_of_orderOf_eq_four {s : ℕ} [Fact s.Prime] {f y : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hfC : f ∉ Subgroup.centralizer (Q : Set G))
    (hy : ∃ k : ℕ, y ^ p ^ k = 1) (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hyz : y * z = z * y) (hyf : y * f = f * y) (hQ5 : Nat.card Q = p ^ 5) :
    Xsubgroup Q z y hZ = Q := by
  classical
  have hXle : Xsubgroup Q z y hZ ≤ Q := Xsubgroup_le Q z y hZ
  have hzX : z ∈ Xsubgroup Q z y hZ := z_mem_Xsubgroup hZ hyz
  obtain ⟨j, hj_pos, hj_le, hXcard, hcongj⟩ :=
    exists_card_Xsubgroup_eq_pow_and_modEq_one hz hQQ hZ hQ hps hf hfQ hfz hfC hyz hyf hQ5
  have hyp : IsPGroup p (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hy
  obtain ⟨x0, hx0X, hx0Z⟩ :=
    exists_mem_Xsubgroup_not_mem_zpowers hz hZ hyz hyQ hyp hQ5
  have hXne : Xsubgroup Q z y hZ ≠ Subgroup.zpowers z := by
    intro h
    exact hx0Z (h ▸ hx0X)
  have hj5 : j = 5 :=
    eq_five_of_card_eq_pow_of_modEq_one hz (Subgroup.zpowers_le.mpr hzX) hXcard hj_le hcongj hXne
  refine Subgroup.eq_of_le_of_card_ge hXle ?_
  rw [hXcard, hj5, hQ5]

omit [Finite G] in
private lemma inf_centralizer_inf_centralizer_eq_zpowers {f y : G}
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hfz : f * z = z * f) (hyz : y * z = z * y)
    (hCf : Q ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z) :
    (Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) ⊓
      Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z := by
  have hzQ : z ∈ Q := (hZ ▸ Subgroup.mem_zpowers z).1
  have hzCf : z ∈ Subgroup.centralizer ({f} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hfz.symm
  have hzCy : z ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hyz.symm
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxQy, hxf⟩ := Subgroup.mem_inf.mp hx
    exact hCf ▸ ⟨(Subgroup.mem_inf.mp hxQy).1, hxf⟩
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.zpowers_le.mpr hzCf hx⟩
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.zpowers_le.mpr hzQ hx, Subgroup.zpowers_le.mpr hzCy hx⟩

omit [Fact (Nat.Prime p)] in
private lemma false_of_card_eq_pow_four_of_modEq {s : ℕ} [Fact s.Prime] {f : G} {K : Subgroup G}
    (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfK : f ∈ Subgroup.normalizer (K : Set G))
    (hKcard : Nat.card K = p ^ 4) (hzcard : Nat.card (Subgroup.zpowers z) = p)
    (hKinf : K ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z) : False := by
  have hmodK := card_modEq_card_inf_centralizer (K := K) (u := f) hf hfK
  have hmod4 : p ^ 4 ≡ p ^ 1 [MOD s] := by
    rw [hKcard, hKinf, hzcard] at hmodK
    simpa using hmodK
  have hcong41 : 4 ≡ 1 [MOD 4] := modEq_of_pow_modEq hps (by norm_num) hmod4
  rw [Nat.ModEq] at hcong41
  norm_num at hcong41

private lemma mem_centralizer_of_X_eq_Q {s : ℕ} [Fact s.Prime] {f y : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hfC : f ∉ Subgroup.centralizer (Q : Set G)) (hQ5 : Nat.card Q = p ^ 5)
    (hyz : y * z = z * y) (hyf : y * f = f * y)
    (hXQ : Xsubgroup Q z y hZ = Q) :
    y ∈ Subgroup.centralizer (Q : Set G) := by
  classical
  obtain ⟨⟨-, hzC⟩, hzcard⟩ := z_mem_inf_centralizer_and_card hz hZ
  have hCf : Q ⊓ Subgroup.centralizer ({f} : Set G) = Subgroup.zpowers z :=
    inf_centralizer_eq_zpowers_of_orderOf_eq_four hz hQQ hZ hQ hps hf hfQ hfz hfC
  have hXall : ∀ x ∈ Q, ⁅x, y⁆ ∈ Subgroup.zpowers z := by
    intro x hx
    exact ((hXQ.symm ▸ hx : x ∈ Xsubgroup Q z y hZ)).2
  by_contra hyC
  have hXall' : ∀ x ∈ Q, ⁅y, x⁆ ∈ Subgroup.zpowers z := by
    intro x hx
    have h := (Subgroup.zpowers z).inv_mem (hXall x hx)
    rwa [commutatorElement_inv] at h
  have hKy := card_inf_centralizer_mul_prime_of_comm (a := y) hz hzC hXall' hyC
  have hKy' : Nat.card (Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) * p = p ^ 5 := by
    rw [hQ5] at hKy
    exact hKy
  have hKcard : Nat.card (Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) = p ^ 4 :=
    card_eq_pow_four_of_card_mul_prime hKy'
  have hfK : f ∈ Subgroup.normalizer
      ((Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf_centralizer (K := Q) hfQ hyf.symm
  have hKinf := inf_centralizer_inf_centralizer_eq_zpowers hZ hfz hyz hCf
  exact false_of_card_eq_pow_four_of_modEq hps hf hfK hKcard hzcard hKinf

theorem mem_centralizer_of_orderOf_eq_four {s : ℕ} [Fact s.Prime] {f y : G}
    (hz : orderOf z = p) (hQQ : ⁅Q, Q⁆ ≤ Subgroup.zpowers z)
    (hZ : Q ⊓ Subgroup.centralizer (Q : Set G) = Subgroup.zpowers z)
    (hQ : Nat.card Q ∣ p ^ 6) (hps : orderOf (p : ZMod s) = 4) (hf : orderOf f = s)
    (hfQ : f ∈ Subgroup.normalizer (Q : Set G)) (hfz : f * z = z * f)
    (hfC : f ∉ Subgroup.centralizer (Q : Set G)) (hy : ∃ k : ℕ, y ^ p ^ k = 1)
    (hyQ : y ∈ Subgroup.normalizer (Q : Set G)) (hyz : y * z = z * y) (hyf : y * f = f * y) :
    y ∈ Subgroup.centralizer (Q : Set G) := by
  have hQ5 := card_eq_pow_five_of_orderOf_eq_four hz hQQ hZ hQ hps hf hfQ hfz hfC
  have hXQ := X_eq_Q_of_orderOf_eq_four hz hQQ hZ hQ hps hf hfQ hfz hfC hy hyQ hyz hyf hQ5
  exact mem_centralizer_of_X_eq_Q hz hQQ hZ hQ hps hf hfQ hfz hfC hQ5 hyz hyf hXQ

end CFSG.Extraspecial

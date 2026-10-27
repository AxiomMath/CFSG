module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.N204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem pow_conj_eq {c p : G} (hq : Commute c ⁅c, p⁆) (k : ℕ) :
    c ^ k * p * (c ^ k)⁻¹ = ⁅c, p⁆ ^ k * p := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : c ^ (k + 1) * p * (c ^ (k + 1))⁻¹ = c * (c ^ k * p * (c ^ k)⁻¹) * c⁻¹ := by
      group
    have h2 : c * (⁅c, p⁆ ^ k * p) * c⁻¹ = ⁅c, p⁆ ^ k * (c * p * c⁻¹) := by
      have := (Commute.pow_right hq k).eq
      calc c * (⁅c, p⁆ ^ k * p) * c⁻¹ = (c * ⁅c, p⁆ ^ k) * p * c⁻¹ := by group
        _ = (⁅c, p⁆ ^ k * c) * p * c⁻¹ := by rw [this]
        _ = ⁅c, p⁆ ^ k * (c * p * c⁻¹) := by group
    have h3 : c * p * c⁻¹ = ⁅c, p⁆ * p := by simp [commutatorElement_def]
    rw [h1, ih, h2, h3, pow_succ]
    group

theorem eq_one_of_odd_of_centralizes [Finite G] {X Q₀ : Subgroup G} (hX : CharTwo X) {c : G}
    (hcX : c ∈ X) (hodd : Odd (orderOf c)) (hcQ : ∀ q ∈ Q₀, c * q = q * c)
    (hcP : ∀ p ∈ pCoreOf 2 X, ⁅c, p⁆ ∈ Q₀) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCoreOf 2 X with hP
  have hPn : X ≤ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 X
  have hcop : ∀ a : ℕ, Nat.Coprime (orderOf c) (2 ^ a) := fun a =>
    (Nat.coprime_two_right.mpr hodd).pow_right a
  have hcomm : ∀ p ∈ P, c * p = p * c := by
    intro p hp
    set q := ⁅c, p⁆ with hqdef
    have hqQ : q ∈ Q₀ := hcP p hp
    have hq : Commute c q := hcQ q hqQ
    have hqP : q ∈ P := by
      have h1 : c * p * c⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hPn hcX) p).mp hp
      have : q = (c * p * c⁻¹) * p⁻¹ := by simp [hqdef, commutatorElement_def]
      rw [this]
      exact P.mul_mem h1 (P.inv_mem hp)
    have hpow := pow_conj_eq hq (orderOf c)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
    have hqm : q ^ orderOf c = 1 := by
      have : q ^ orderOf c * p = 1 * p := by rw [← hpow, one_mul]
      exact mul_right_cancel this
    obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 X) ⟨q, hqP⟩
    have hqa : q ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have h1 : orderOf q ∣ orderOf c := orderOf_dvd_of_pow_eq_one hqm
    have h2 : orderOf q ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hqa
    have h3 : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes (hcop a) h1 h2
    have hq1 : q = 1 := orderOf_eq_one_iff.mp h3
    rw [hqdef, commutatorElement_eq_one_iff_mul_comm] at hq1
    exact hq1
  have hcC : c ∈ X ⊓ Subgroup.centralizer (P : Set G) :=
    ⟨hcX, Subgroup.mem_centralizer_iff.mpr fun p hp => (hcomm p hp).symm⟩
  have hcPm : c ∈ P := hX hcC
  obtain ⟨b, hb⟩ := (pCoreOf_isPGroup 2 X) ⟨c, hcPm⟩
  have hcb : c ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have h1 : orderOf c ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hcb
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hcop b) dvd_rfl h1)

theorem exists_pow_mul_mem {N : Subgroup G} {n s : G} (hn : n ∈ N)
    (hs : s ∈ Subgroup.normalizer (N : Set G)) (k : ℕ) :
    ∃ n' ∈ N, (n * s) ^ k = n' * s ^ k := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨n', hn', h⟩ := ih
    have hsk : s ^ k ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ hs k
    have h1 : s ^ k * n * (s ^ k)⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp hsk n).mp hn
    refine ⟨n' * (s ^ k * n * (s ^ k)⁻¹), N.mul_mem hn' h1, ?_⟩
    rw [pow_succ, h]
    group

theorem mem_of_odd_of_mem_sup {N S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) {c : G} (hc : c ∈ N ⊔ S)
    (hodd : Odd (orderOf c)) : c ∈ N := by
  have hmul : ((N ⊔ S : Subgroup G) : Set G) = (N : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left N S hSN
  have hc' : c ∈ (N : Set G) * (S : Set G) := by rw [← hmul]; exact hc
  obtain ⟨n, hn, s, hs, rfl⟩ := hc'
  obtain ⟨n', hn', h⟩ := exists_pow_mul_mem hn (hSN hs) (orderOf (n * s))
  rw [pow_orderOf_eq_one] at h
  have hsm : s ^ orderOf (n * s) ∈ N := by
    have : s ^ orderOf (n * s) = n'⁻¹ := by
      have : n' * s ^ orderOf (n * s) = 1 := h.symm
      exact eq_inv_of_mul_eq_one_right this
    rw [this]
    exact N.inv_mem hn'
  obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
  have hsa : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hcop : IsCoprime (orderOf (n * s) : ℤ) ((2 ^ a : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_two_right.mpr hodd).pow_right a)
  obtain ⟨u, v, huv⟩ := hcop
  have hsN : s ∈ N := by
    have : s = (s ^ orderOf (n * s)) ^ u * (s ^ 2 ^ a) ^ v := by
      rw [← zpow_natCast s (orderOf (n * s)), ← zpow_natCast s (2 ^ a), ← zpow_mul, ← zpow_mul,
        ← zpow_add]
      have e : ((orderOf (n * s) : ℕ) : ℤ) * u + ((2 ^ a : ℕ) : ℤ) * v = 1 := by linarith
      rw [e, zpow_one]
    rw [this, hsa, one_zpow, mul_one]
    exact Subgroup.zpow_mem _ (by simpa using hsm) u
  exact N.mul_mem hn hsN

theorem exists_conj_mem_of_not_dvd [Finite G] {N H : Subgroup G} {p : ℕ} [hp : Fact p.Prime]
    (hidx : ¬ p ∣ H.relIndex N) {c : G} (hcN : c ∈ N) {k : ℕ} (hck : c ^ p ^ k = 1) :
    ∃ g ∈ N, g⁻¹ * c * g ∈ H := by
  let c' : ↥N := ⟨c, hcN⟩
  let K : Subgroup ↥N := Subgroup.zpowers c'
  have hc'k : c' ^ p ^ k = 1 := Subtype.ext (by simpa using hck)
  have hK : IsPGroup p K := by
    intro x
    obtain ⟨x, j, rfl⟩ := x
    refine ⟨k, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc'k, one_zpow]
  have hmod := hK.card_modEq_card_fixedPoints (α := ↥N ⧸ H.subgroupOf N)
  have hcard : Nat.card (↥N ⧸ H.subgroupOf N) = H.relIndex N := rfl
  have hne : Nat.card (MulAction.fixedPoints ↥K (↥N ⧸ H.subgroupOf N)) ≠ 0 := by
    intro h0
    rw [h0] at hmod
    exact hidx ((Nat.modEq_zero_iff_dvd).mp (hcard ▸ hmod.symm.symm))
  obtain ⟨⟨x, hx⟩⟩ := Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hne) |>.1
  induction x using QuotientGroup.induction_on with
  | H g =>
    have h1 : (⟨c', Subgroup.mem_zpowers c'⟩ : K) • (QuotientGroup.mk g : ↥N ⧸ H.subgroupOf N) =
        QuotientGroup.mk g := MulAction.mem_fixedPoints.mp hx ⟨c', Subgroup.mem_zpowers c'⟩
    have h2 : (⟨c', Subgroup.mem_zpowers c'⟩ : K) • (QuotientGroup.mk g : ↥N ⧸ H.subgroupOf N) =
        QuotientGroup.mk (c' * g) := rfl
    rw [h2, QuotientGroup.eq] at h1
    refine ⟨g.1, g.2, ?_⟩
    have h4 : (((c' * g)⁻¹ * g : ↥N) : G) ∈ H := h1
    have h5 : g.1⁻¹ * c * g.1 = ((((c' * g)⁻¹ * g : ↥N) : G))⁻¹ := by
      simp [c', mul_assoc]
    rw [h5]
    exact H.inv_mem h4

end CFSG.Quasithin.N204

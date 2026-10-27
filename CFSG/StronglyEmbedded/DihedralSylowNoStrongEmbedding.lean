module

public import CFSG.Open.FusionDefs
import CFSG.StronglyEmbedded.BenderNormalSeries
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Timmesfeld.Closure.Bender

public section

namespace CFSG.StronglyEmbedded

open CFSG.Open
open scoped MatrixGroups

theorem not_commute_dihedralGroup_r_one_sr_zero {m : ℕ} (hm : 3 ≤ m) :
    ¬ Commute (DihedralGroup.r (1 : ZMod m)) (DihedralGroup.sr 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 3 := ⟨m - 3, by omega⟩
  intro h
  have h' := h.eq
  rw [DihedralGroup.r_mul_sr, zero_sub, DihedralGroup.sr_mul_r, zero_add, DihedralGroup.sr.injEq,
    neg_eq_iff_add_eq_zero, one_add_one_eq_two, ← ZMod.val_eq_zero, ZMod.val_two_eq_two_mod] at h'
  simpa using Nat.le_of_dvd Nat.zero_lt_two <| Nat.dvd_of_mod_eq_zero h'

theorem commute_quaternionGroup_of_orderOf_eq_two {n : ℕ} [NeZero n] {x : QuaternionGroup n}
    (hx : orderOf x = 2) (y : QuaternionGroup n) : Commute y x := by
  cases x with
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hx
    exact absurd hx (by norm_num)
  | a i =>
    have h2 : QuaternionGroup.a i * QuaternionGroup.a i = 1 := by
      rw [← pow_two, ← hx, pow_orderOf_eq_one]
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq] at h2
    cases y with
    | a j =>
      show QuaternionGroup.a j * QuaternionGroup.a i = QuaternionGroup.a i * QuaternionGroup.a j
      rw [QuaternionGroup.a_mul_a, QuaternionGroup.a_mul_a, add_comm]
    | xa j =>
      show QuaternionGroup.xa j * QuaternionGroup.a i = QuaternionGroup.a i * QuaternionGroup.xa j
      rw [QuaternionGroup.xa_mul_a, QuaternionGroup.a_mul_xa, sub_eq_add_neg,
        neg_eq_of_add_eq_zero_right h2]

section Elements

variable {Y : Type*} [Group Y]

theorem mem_of_pow_two_pow_eq_one_of_odd_index {N : Subgroup Y} [N.Normal] (hN : Odd N.index)
    {x : Y} {k : ℕ} (hx : x ^ 2 ^ k = 1) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) N.index :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hN)
  exact (QuotientGroup.eq_one_iff x).mp
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))

theorem eq_one_of_pow_two_pow_eq_one_of_mem {M : Subgroup Y} (hM : Odd (Nat.card M)) {x : Y}
    (hxM : x ∈ M) {k : ℕ} (hx : x ^ 2 ^ k = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ k) (Nat.card M) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hM)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
    (orderOf_dvd_of_pow_eq_one hx) (Subgroup.orderOf_dvd_natCard M hxM))

end Elements

private theorem fusionStronglyEmbedded_normalizer_of_fusionIsBenderGroup {K : Type*} [Group K]
    [Finite K] (hK : fusionIsBenderGroup K) (Q : Sylow 2 K) :
    fusionStronglyEmbedded (Subgroup.normalizer ((Q : Subgroup K) : Set K)) := by
  rcases hK with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv _ e.toEquiv
    exact ((bender_psl2_borel_full f hf).map_mulEquiv e.symm Q).1
  · have : Finite (PSU3 2 f) := Finite.of_equiv _ e.toEquiv
    exact ((bender_psu3_borel_full f hf).map_mulEquiv e.symm Q).1
  · have : Finite (Sz a) := Finite.of_equiv _ e.toEquiv
    exact ((bender_suzuki_borel_full a ha).map_mulEquiv e.symm Q).1

theorem commute_of_isPGroup_of_bender_section {Y : Type*} [Group Y] [Finite Y]
    {M N : Subgroup Y} [N.Normal] [(M.subgroupOf N).Normal] (hModd : Odd (Nat.card M))
    (hNodd : Odd N.index) (hB : fusionIsBenderGroup (N ⧸ M.subgroupOf N)) {P : Subgroup Y}
    (hP : IsPGroup 2 P) {s t : Y} (hsP : s ∈ P) (hs : orderOf s = 2) (htP : t ∈ P) :
    Commute t s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpow : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hPN : P ≤ N := fun x hx => by
    obtain ⟨k, hk⟩ := hpow x hx
    exact mem_of_pow_two_pow_eq_one_of_odd_index hNodd hk
  let π : N →* N ⧸ M.subgroupOf N := QuotientGroup.mk' (M.subgroupOf N)
  let s' : N := ⟨s, hPN hsP⟩
  let t' : N := ⟨t, hPN htP⟩
  obtain ⟨Q, hQ⟩ := (hP.comap_subtype (K := N)).map π |>.exists_le_sylow
  have hsQ : π s' ∈ (Q : Subgroup (N ⧸ M.subgroupOf N)) :=
    hQ (Subgroup.mem_map_of_mem π (show s' ∈ P.subgroupOf N from hsP))
  have htQ : π t' ∈ (Q : Subgroup (N ⧸ M.subgroupOf N)) :=
    hQ (Subgroup.mem_map_of_mem π (show t' ∈ P.subgroupOf N from htP))
  have hs2 : s ^ 2 ^ 1 = 1 := by rw [pow_one, ← hs, pow_orderOf_eq_one]
  have hsM : s ∉ M := fun h => by
    rw [eq_one_of_pow_two_pow_eq_one_of_mem hModd h hs2, orderOf_one] at hs
    exact absurd hs (by norm_num)
  have hπs : orderOf (π s') = 2 := by
    refine orderOf_eq_prime ?_ fun h => hsM ((QuotientGroup.eq_one_iff s').mp h)
    rw [← map_pow, show s' ^ 2 = 1 from Subtype.ext (by simpa using hs2), map_one]
  have hc : Commute (π t') (π s') := CFSG.Timmesfeld.Connectivity.commute_of_mem_sylow Q
    (fusionStronglyEmbedded_normalizer_of_fusionIsBenderGroup hB Q) hsQ hπs htQ
  have hker : (s' * t')⁻¹ * (t' * s') ∈ M.subgroupOf N :=
    QuotientGroup.eq.mp (show π (s' * t') = π (t' * s') by rw [map_mul, map_mul, hc.eq])
  have hcP : (s * t)⁻¹ * (t * s) ∈ P :=
    P.mul_mem (P.inv_mem (P.mul_mem hsP htP)) (P.mul_mem htP hsP)
  obtain ⟨k, hk⟩ := hpow _ hcP
  exact (inv_mul_eq_one.mp (eq_one_of_pow_two_pow_eq_one_of_mem hModd hker hk)).symm

theorem commute_of_mem_sylow_of_fusionStronglyEmbedded {Y : Type*} [Group Y] [Finite Y]
    {H : Subgroup Y} (hH : fusionStronglyEmbedded H) (P : Sylow 2 Y) {s t : Y}
    (hsP : s ∈ (P : Subgroup Y)) (hs : orderOf s = 2) (htP : t ∈ (P : Subgroup Y)) :
    Commute t s := by
  rcases bender_strongly_embedded_normal_series Y H hH with hcq |
    ⟨M, N, -, hN, hMN, -, hModd, hNodd, hB⟩
  · let s' : (P : Subgroup Y) := ⟨s, hsP⟩
    let t' : (P : Subgroup Y) := ⟨t, htP⟩
    suffices h : Commute t' s' from congrArg Subtype.val h
    rcases hcq P with hcyc | ⟨r, -, ⟨φ⟩⟩
    · exact (IsCyclic.isMulCommutative (α := (P : Subgroup Y))).is_comm.comm t' s'
    · have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
      have hφs : orderOf (φ s') = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hs]
      simpa using (commute_quaternionGroup_of_orderOf_eq_two hφs (φ t')).map φ.symm
  · exact commute_of_isPGroup_of_bender_section hModd hNodd hB P.isPGroup' hsP hs htP

theorem not_fusionStronglyEmbedded_of_sylow_mulEquiv_dihedralGroup {Y : Type*} [Group Y]
    [Finite Y] (P : Sylow 2 Y) {m : ℕ} (hm : 3 ≤ m) (e : (P : Subgroup Y) ≃* DihedralGroup m)
    (H : Subgroup Y) : ¬ fusionStronglyEmbedded H := by
  intro hH
  let s : (P : Subgroup Y) := e.symm (DihedralGroup.sr 0)
  let t : (P : Subgroup Y) := e.symm (DihedralGroup.r 1)
  have hs : orderOf (s : Y) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have h : Commute t s :=
    Subtype.ext (commute_of_mem_sylow_of_fusionStronglyEmbedded hH P s.2 hs t.2)
  exact not_commute_dihedralGroup_r_one_sr_zero hm (by simpa [s, t] using h.map e)

end CFSG.StronglyEmbedded

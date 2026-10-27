module

public import CFSG.Quasithin.Background.FLcGrp
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.A38c8

open CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem le_inner_of_isPGroup_two_odd {H : Type*} [Group H] (hodd : Odd (Nat.card (Outer H)))
    (P : Subgroup (MulAut H)) (hP : IsPGroup 2 P) : P ≤ inner H := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have h1 : orderOf (x : Outer H) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hk', QuotientGroup.mk_one])
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Outer H)) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
  have h3 : orderOf (x : Outer H) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 (orderOf_dvd_natCard _)
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).1 h3

theorem exists_inner_of_odd_outer {Y : Type*} [Group Y] {N : Subgroup Y} [N.Normal]
    (hodd : Odd (Nat.card (Outer ↥N))) {t : Y} {a : ℕ} (ht : t ^ 2 ^ a = 1) :
    ∃ n ∈ N, ∀ x ∈ N, t * x * t⁻¹ = n * x * n⁻¹ := by
  set α : MulAut ↥N := MulAut.conjNormal t
  have hα : α ^ 2 ^ a = 1 := by rw [← map_pow, ht, map_one]
  have hP : IsPGroup 2 (Subgroup.zpowers α) := by
    rintro ⟨g, i, rfl⟩
    refine ⟨a, Subtype.ext ?_⟩
    change (α ^ i) ^ 2 ^ a = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  obtain ⟨j, hj⟩ := le_inner_of_isPGroup_two_odd hodd _ hP (Subgroup.mem_zpowers α)
  refine ⟨(j : Y), j.2, fun x hx => ?_⟩
  have h := congrArg Subtype.val (DFunLike.congr_fun hj ⟨x, hx⟩)
  simp [α, MulAut.conjNormal_apply] at h
  exact h.symm

theorem pow_eq_one_of_conj_eq_of_center_eq_bot {Y : Type} [Group Y] {N : Subgroup Y}
    (hZ : Subgroup.center ↥N = ⊥) {t n : Y} (hn : n ∈ N)
    (hconj : ∀ x ∈ N, t * x * t⁻¹ = n * x * n⁻¹) {m : ℕ} (ht : t ^ m = 1) : n ^ m = 1 := by
  have hc : ∀ x ∈ N, Commute (n⁻¹ * t) x := by
    intro x hx
    have := hconj x hx
    show n⁻¹ * t * x = x * (n⁻¹ * t)
    calc n⁻¹ * t * x = n⁻¹ * (t * x * t⁻¹) * t := by group
      _ = n⁻¹ * (n * x * n⁻¹) * t := by rw [this]
      _ = x * (n⁻¹ * t) := by group
  have htn : t = n * (n⁻¹ * t) := by group
  have hnc : Commute n (n⁻¹ * t) := (hc n hn).symm
  have hpow : n ^ m * (n⁻¹ * t) ^ m = 1 := by
    rw [← hnc.mul_pow, ← htn, ht]
  have hz : n ^ m = ((n⁻¹ * t) ^ m)⁻¹ := eq_inv_of_mul_eq_one_left hpow
  have hzN : n ^ m ∈ N := N.pow_mem hn m
  have hmem : (⟨n ^ m, hzN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : Y) * n ^ m = n ^ m * (g : Y)
    rw [hz]
    exact ((((hc g g.2).pow_left m).inv_left).symm).eq
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem mem_normalizer_of_conj_eq_on_le {Y : Type} [Group Y] {N B : Subgroup Y} (hBN : B ≤ N)
    {t n : Y} (hn : n ∈ N) (hconj : ∀ x ∈ N, t * x * t⁻¹ = n * x * n⁻¹)
    (ht : t ∈ Subgroup.normalizer (B : Set Y)) : n ∈ Subgroup.normalizer (B : Set Y) := by
  rw [Subgroup.mem_normalizer_iff] at ht ⊢
  intro x
  constructor
  · intro hx
    rw [← hconj x (hBN hx)]
    exact (ht x).1 hx
  · intro hx
    have hxN : x ∈ N := by
      have := N.mul_mem (N.mul_mem (N.inv_mem hn) (hBN hx)) hn
      simpa [mul_assoc] using this
    rw [← hconj x hxN] at hx
    exact (ht x).2 hx

theorem exists_mem_inf_inner_of_odd_outer {Y : Type} [Group Y] [Finite Y] {N T : Subgroup Y}
    (hN : N.Normal) (hT : IsSylowTwoOf T ⊤) (hZ : Subgroup.center ↥N = ⊥)
    (hodd : Odd (Nat.card (Outer ↥N))) :
    ∀ t ∈ T, ∃ x ∈ T ⊓ N, ∀ y ∈ N, t * y * t⁻¹ = x * y * x⁻¹ := by
  intro t ht
  obtain ⟨a, ha⟩ : ∃ a : ℕ, t ^ 2 ^ a = 1 := by
    obtain ⟨a, ha⟩ := hT.2.1 ⟨t, ht⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  obtain ⟨n, hnN, hconj⟩ := exists_inner_of_odd_outer hodd ha
  have hn2 : n ^ 2 ^ a = 1 := pow_eq_one_of_conj_eq_of_center_eq_bot hZ hnN hconj ha
  have hT₀ : IsSylowTwoOf (T ⊓ N) N :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hT le_top (fun x _ =>
      Subgroup.normalizer_eq_top_iff.2 hN ▸ Subgroup.mem_top x)
  have hnor : n ∈ Subgroup.normalizer ((T ⊓ N : Subgroup Y) : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← hconj y (Subgroup.mem_inf.1 hy).2]
      exact Subgroup.mem_inf.2 ⟨T.mul_mem (T.mul_mem ht (Subgroup.mem_inf.1 hy).1) (T.inv_mem ht),
        hN.conj_mem y (Subgroup.mem_inf.1 hy).2 t⟩
    · intro hy
      have hyN : y ∈ N := by
        have := hN.conj_mem _ (Subgroup.mem_inf.1 hy).2 n⁻¹
        simpa [mul_assoc] using this
      rw [← hconj y hyN] at hy
      have hyT : y ∈ T := by
        have := T.mul_mem (T.mul_mem (T.inv_mem ht) (Subgroup.mem_inf.1 hy).1) ht
        simpa [mul_assoc] using this
      exact Subgroup.mem_inf.2 ⟨hyT, hyN⟩
  have hZp : IsPGroup 2 ↥(Subgroup.zpowers n) := by
    obtain ⟨j, hj, hjn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn2)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hjn])
  have hle : Subgroup.zpowers n ≤ T ⊓ N :=
    FLc.le_of_normalizes_of_sylow hT₀ le_rfl inf_le_right ((Subgroup.zpowers_le).2 hnN) hZp
      ((Subgroup.zpowers_le).2 hnor)
  exact ⟨n, hle (Subgroup.mem_zpowers n), hconj⟩

end CFSG.Quasithin.A38c8

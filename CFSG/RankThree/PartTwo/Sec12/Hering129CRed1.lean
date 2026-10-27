module

import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.LocalRank.PrimeComplementCentralizesNormal
import CFSG.RankThree.PartTwo.KFacts.KS116Lin
import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Hering129C

theorem isSubnormal_subgroupOf_of_le {Z : Type*} [Group Z] {H A B : Subgroup Z} (hAB : A ≤ B)
    (h : (H.subgroupOf B).IsSubnormal) : (H.subgroupOf A).IsSubnormal := by
  have h1 := h.comap (Subgroup.inclusion hAB)
  have h2 : (H.subgroupOf B).comap (Subgroup.inclusion hAB) = H.subgroupOf A := by
    ext a
    simp [Subgroup.mem_subgroupOf]
  rwa [h2] at h1

theorem isSubnormal_map_subgroupOf {A B : Type*} [Group A] [Group B] (f : A →* B)
    {V S : Subgroup A} (hSV : S ≤ V) (hsub : (S.subgroupOf V).IsSubnormal) :
    ((S.map f).subgroupOf (V.map f)).IsSubnormal := by
  have hsurj := f.subgroupMap_surjective V
  have h1 := hsub.map hsurj
  have h2 : (S.subgroupOf V).map (f.subgroupMap V) = (S.map f).subgroupOf (V.map f) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hvS, hvz⟩
      refine ⟨⟨v, hSV hvS⟩, hvS, ?_⟩
      exact Subtype.ext hvz
  rwa [h2] at h1

theorem isSubnormal_subgroupOf_subgroupOf {Z : Type*} [Group Z] {H N K : Subgroup Z}
    (hNK : N ≤ K) (h : (H.subgroupOf N).IsSubnormal) :
    ((H.subgroupOf K).subgroupOf (N.subgroupOf K)).IsSubnormal := by
  let e := Subgroup.subgroupOfEquivOfLe hNK
  have h1 := h.comap (e : N.subgroupOf K →* N)
  have h2 : (H.subgroupOf N).comap (e : N.subgroupOf K →* N) =
      (H.subgroupOf K).subgroupOf (N.subgroupOf K) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact Iff.rfl
  rwa [h2] at h1

theorem eq_one_of_pow_three_pow_of_mem {Y : Type*} [Group Y] [Finite Y] {N : Subgroup Y}
    (hN : ¬ 3 ∣ Nat.card N) {x : Y} (hxN : x ∈ N) {r : ℕ} (hx : x ^ 3 ^ r = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 ^ r := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hxN]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (3 ^ r) (Nat.card N) :=
    Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_three_part_lift {Y Z : Type*} [Group Y] [Finite Y] [Group Z] (ψ : Y →* Z) {y : Y}
    (hy : ψ y ^ 3 = 1) :
    ∃ s ∈ Subgroup.zpowers y, (∃ r : ℕ, s ^ 3 ^ r = 1) ∧ ψ s = ψ y := by
  obtain ⟨r, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' 3 (by norm_num)
  refine ⟨y ^ (m * m), Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _, ⟨r, ?_⟩, ?_⟩
  · rw [← pow_mul, show m * m * 3 ^ r = (3 ^ r * m) * m by ring, ← hn, pow_mul,
      pow_orderOf_eq_one, one_pow]
  · have hmm : m * m % 3 = 1 := by
      have : m % 3 = 1 ∨ m % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    rw [map_pow, ← Nat.div_add_mod (m * m) 3, hmm, pow_add, pow_mul, hy, one_pow, one_mul,
      pow_one]

theorem eq_one_of_mk_eq_one {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {x : Y} (hx : x ^ 3 = 1) (h : QuotientGroup.mk' N x = 1) :
    x = 1 := by
  have := (QuotientGroup.eq_one_iff x).mp h
  simpa using eq_one_of_pow_three_pow_of_mem hN this (r := 1) (by simpa using hx)

theorem orderOf_mk_eq_three {Y : Type*} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {x : Y} (hx : x ^ 3 = 1) (hx1 : x ≠ 1) :
    orderOf (QuotientGroup.mk' N x) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, hx, map_one]
  · intro h
    exact hx1 (eq_one_of_mk_eq_one N hN hx h)

theorem isElemAbelian_sup_zpowers_three {Y : Type*} [Group Y] {A : Subgroup Y}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {t : Y} (ht3 : t ^ 3 = 1)
    (ht : ∀ d ∈ A, d * t = t * d) :
    CFSG.Assembly.IsElemAbelian 3 (A ⊔ Subgroup.zpowers t) := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hnorm : Subgroup.zpowers t ≤ Subgroup.normalizer (A : Set Y) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer (A : Set Y) (Subgroup.mem_centralizer_iff.mpr
      fun d hd => ht d hd)
  have hdec : ∀ x ∈ A ⊔ Subgroup.zpowers t, ∃ e ∈ A, ∃ k : ℤ, x = e * t ^ k := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A _ hnorm] at hx
    obtain ⟨e, he, y, hy, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨e, he, k, rfl⟩
  have hcomm : ∀ e ∈ A, ∀ k : ℤ, Commute e (t ^ k) := fun e he k =>
    Commute.zpow_right (ht e he) k
  have ht3' : ∀ k : ℤ, (t ^ k) ^ 3 = 1 := fun k => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht3, one_zpow]
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨e, he, k, hk⟩ := hdec x.1 x.2
    obtain ⟨f, hf, l, hl⟩ := hdec y.1 y.2
    apply Subtype.ext
    show (x : Y) * y = y * x
    rw [hk, hl]
    have h1 : Commute e f := hAc e he f hf
    have h2 : Commute (t ^ k) f := (hcomm f hf k).symm
    have h3 : Commute (t ^ k) (t ^ l) := (Commute.refl t).zpow_zpow _ _
    exact (Commute.mul_left (Commute.mul_right h1 (hcomm e he l))
      (Commute.mul_right h2 h3)).eq
  · obtain ⟨e, he, k, hk⟩ := hdec x hx
    have hc : Commute e (t ^ k) := hcomm e he k
    rw [hk, hc.mul_pow, hA.2 e he, ht3', one_mul]

theorem mem_of_maximal_elemAbelian {Y : Type*} [Group Y] {A : Subgroup Y}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ B : Subgroup Y, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) {t : Y}
    (ht3 : t ^ 3 = 1) (ht : ∀ d ∈ A, d * t = t * d) : t ∈ A := by
  have h := hmax _ (isElemAbelian_sup_zpowers_three hA ht3 ht) le_sup_left
  rw [← h]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)


theorem isPGroup_zpowers_three {Λ : Type*} [Group Λ] {c : Λ} (hc : c ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers c) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hc) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem exists_zpow_mul_of_mem_sup_commute {Y : Type*} [Group Y] [Finite Y] {E F : Subgroup Y}
    {x : Y} (hEdec : E = Subgroup.zpowers x ⊔ F) (hxF : ∀ f ∈ F, x * f = f * x) :
    ∀ e ∈ E, ∃ k : ℤ, ∃ f ∈ F, e = x ^ k * f := by
  intro e he
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) F (fun u hu v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left (hxF v hv) k).eq)
  have he' : e ∈ ((Subgroup.zpowers x ⊔ F : Subgroup Y) : Set Y) := hEdec ▸ he
  rw [hset] at he'
  obtain ⟨u, hu, f, hf, rfl⟩ := he'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨k, f, hf, rfl⟩

theorem isElemAbelian_zpowers_three {Y : Type*} [Group Y] {x : Y} (hx : x ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x) := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun u hu => ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp u.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp v.2
    apply Subtype.ext
    show (u : Y) * v = v * u
    rw [← hi, ← hj]
    exact (Commute.zpow_zpow_self x i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

theorem isElemAbelian_zpowers_sup_three {Y : Type*} [Group Y] {x y : Y} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hxy : x * y = y * x) :
    CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers y) :=
  isElemAbelian_sup_zpowers_three (isElemAbelian_zpowers_three hx) hy fun d hd => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact (Commute.zpow_left (show Commute x y from hxy) i).eq

end Hering129C

end CFSG.RankThree.PartTwo.Sec12

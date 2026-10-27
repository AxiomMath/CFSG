module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
import CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2SylQP
import CFSG.GroupTheory.SupCommute
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.NormalCThreeCentral

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open scoped Pointwise

private lemma r891_isMulCommutative_sup_zpowers {X : Type} [Group X] {a b : X}
    (h : Commute a b) : IsMulCommutative ↥(zpowers a ⊔ zpowers b) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure ?_
  intro x hx y hy _
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Subgroup.mul_comm_of_mem_isMulCommutative _ hx hy
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (h.zpow_zpow i j).eq
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (h.symm.zpow_zpow i j).eq
  · exact Subgroup.mul_comm_of_mem_isMulCommutative _ hx hy

private lemma r891_central_of_sup_zpowers {S : Type} [Group S] {T : Subgroup S} {d x : S}
    (hT : ∀ a ∈ T, ∀ c ∈ T, Commute a c) (hd : ∀ a ∈ T, Commute a d)
    (hsup : T ⊔ zpowers d = ⊤) (hx : x ∈ T) : ∀ g : S, g * x = x * g := by
  have hnorm : T ≤ Subgroup.normalizer (zpowers d : Set S) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · rintro ⟨k, rfl⟩
      rw [(hd a ha).zpow_right k |>.eq]
      have h1 : d ^ k * a * a⁻¹ = d ^ k := by group
      rw [h1]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) k
    · intro hc
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
      have hcomm : Commute a⁻¹ (d ^ k) := ((hd a ha).inv_left).zpow_right k
      have h1 : c = a⁻¹ * (a * c * a⁻¹) * a := by group
      have h3 : a⁻¹ * (a * c * a⁻¹) * a = a⁻¹ * d ^ k * a := by rw [hk]
      have h2 : a⁻¹ * d ^ k * a = d ^ k := by rw [hcomm.eq]; group
      rw [h1, h3, h2]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers d) k
  have hset : (↑(T ⊔ zpowers d) : Set S) = (T : Set S) * (zpowers d : Set S) :=
    Subgroup.coe_mul_of_left_le_normalizer_right T (zpowers d) hnorm
  intro g
  have hg : g ∈ (T : Set S) * (zpowers d : Set S) := by
    rw [← hset, hsup]
    exact Subgroup.mem_top g
  obtain ⟨a, ha, c, hc, rfl⟩ := hg
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  have h1 : Commute x (d ^ k) := (hd x hx).zpow_right k
  have h2 : Commute a x := hT a ha x hx
  calc a * d ^ k * x = a * (d ^ k * x) := by rw [mul_assoc]
    _ = a * (x * d ^ k) := by rw [h1.eq]
    _ = a * x * d ^ k := by rw [← mul_assoc]
    _ = x * a * d ^ k := by rw [h2.eq]
    _ = x * (a * d ^ k) := by rw [← mul_assoc]

private lemma r891_zpow_mul_pow {X : Type} [Group X] {a b : X} (h : Commute a b) (i j : ℤ)
    (n : ℕ) : (a ^ i * b ^ j) ^ n = a ^ ((n : ℤ) * i) * b ^ ((n : ℤ) * j) := by
  rw [Commute.mul_pow (h.zpow_zpow i j)]
  congr 1
  · calc (a ^ i) ^ n = (a ^ i) ^ ((n : ℕ) : ℤ) := by rw [zpow_natCast]
      _ = a ^ (i * (n : ℤ)) := by rw [zpow_mul]
      _ = a ^ ((n : ℤ) * i) := by rw [mul_comm]
  · calc (b ^ j) ^ n = (b ^ j) ^ ((n : ℕ) : ℤ) := by rw [zpow_natCast]
      _ = b ^ (j * (n : ℤ)) := by rw [zpow_mul]
      _ = b ^ ((n : ℤ) * j) := by rw [mul_comm]

private lemma r891_dvd_of_zpow_eq_one {X : Type} [Group X] {y : X} {e k : ℕ} {i : ℤ}
    (hy : orderOf y = 3 ^ (e + k)) (h : y ^ ((3 : ℤ) ^ k * i) = 1) :
    ((3 : ℤ) ^ e) ∣ i := by
  have h1 : ((orderOf y : ℕ) : ℤ) ∣ (3 : ℤ) ^ k * i := orderOf_dvd_iff_zpow_eq_one.mpr h
  have h1' : ((3 : ℤ) ^ (e + k)) ∣ (3 : ℤ) ^ k * i := by
    have h' := h1
    rw [hy] at h'
    push_cast at h'
    exact h'
  rw [pow_add] at h1'
  have h2 : (3 : ℤ) ^ k * (3 : ℤ) ^ e ∣ (3 : ℤ) ^ k * i := by
    rw [mul_comm ((3 : ℤ) ^ k) ((3 : ℤ) ^ e)]
    exact h1'
  exact (Int.mul_dvd_mul_iff_left (pow_ne_zero k (by norm_num : (3 : ℤ) ≠ 0))).mp h2

private lemma r891_conj_three {X : Type} [Group X] (φ : MulAut X) {y₀ b₁ : X} {u v : ℤ}
    (hy : φ y₀ = y₀) (hb : φ b₁ = y₀ ^ u * b₁ ^ v) (hc : Commute y₀ b₁) :
    (φ ^ 3) b₁ = y₀ ^ (u * (1 + v + v ^ 2)) * b₁ ^ (v ^ 3) := by
  have hy' : ∀ n : ℤ, φ (y₀ ^ n) = y₀ ^ n := by
    intro n
    rw [map_zpow, hy]
  have hb' : ∀ n : ℤ, φ (b₁ ^ n) = (y₀ ^ u * b₁ ^ v) ^ n := by
    intro n
    rw [map_zpow, hb]
  have h2 : (φ ^ 2) b₁ = y₀ ^ (u + u * v) * b₁ ^ (v ^ 2) := by
    calc (φ ^ 2) b₁ = φ (φ b₁) := rfl
      _ = φ (y₀ ^ u * b₁ ^ v) := by rw [hb]
      _ = φ (y₀ ^ u) * φ (b₁ ^ v) := map_mul ..
      _ = y₀ ^ u * (y₀ ^ u * b₁ ^ v) ^ v := by rw [hy', hb']
      _ = y₀ ^ u * ((y₀ ^ u) ^ v * (b₁ ^ v) ^ v) := by
          rw [Commute.mul_zpow (hc.zpow_zpow u v) v]
      _ = y₀ ^ u * (y₀ ^ (u * v) * b₁ ^ (v * v)) := by rw [← zpow_mul, ← zpow_mul]
      _ = y₀ ^ (u + u * v) * b₁ ^ (v ^ 2) := by
          rw [← mul_assoc, ← zpow_add, ← pow_two]
  calc (φ ^ 3) b₁ = φ ((φ ^ 2) b₁) := rfl
    _ = φ (y₀ ^ (u + u * v) * b₁ ^ (v ^ 2)) := by rw [h2]
    _ = φ (y₀ ^ (u + u * v)) * φ (b₁ ^ (v ^ 2)) := map_mul ..
    _ = y₀ ^ (u + u * v) * (y₀ ^ u * b₁ ^ v) ^ (v ^ 2) := by rw [hy', hb']
    _ = y₀ ^ (u + u * v) * ((y₀ ^ u) ^ (v ^ 2) * (b₁ ^ v) ^ (v ^ 2)) := by
        rw [Commute.mul_zpow (hc.zpow_zpow u v) (v ^ 2)]
    _ = y₀ ^ (u + u * v) * (y₀ ^ (u * v ^ 2) * b₁ ^ (v * v ^ 2)) := by
        rw [← zpow_mul, ← zpow_mul]
    _ = y₀ ^ (u * (1 + v + v ^ 2)) * b₁ ^ (v ^ 3) := by
        rw [← mul_assoc, ← zpow_add,
          show u + u * v + u * v ^ 2 = u * (1 + v + v ^ 2) by ring,
          show v * v ^ 2 = v ^ 3 by ring]

private lemma r891_card_sup_zpowers {G : Type} [Group G] {y b : G} {e : ℕ}
    (hy : orderOf y = 3 ^ (e + 1)) (hb : orderOf b = 3 ^ e) (hyb : Commute y b)
    (hdisj : zpowers y ⊓ zpowers b = ⊥) :
    Nat.card ↥(zpowers y ⊔ zpowers b) = 3 ^ (2 * e + 1) := by
  have hcomm : ∀ a ∈ zpowers y, ∀ c ∈ zpowers b, Commute a c := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact hyb.zpow_zpow i j
  rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, Nat.card_zpowers, Nat.card_zpowers,
    hy, hb, ← pow_add]
  congr 1
  ring

private lemma r891_index_sup_zpowers {G : Type} [Group G] {P : Subgroup G} {y b : G} {e : ℕ}
    (hAle : zpowers y ⊔ zpowers b ≤ P)
    (hcard : Nat.card ↥(zpowers y ⊔ zpowers b) = 3 ^ (2 * e + 1))
    (hP : Nat.card P = 3 ^ (2 * e + 2)) :
    ((zpowers y ⊔ zpowers b).subgroupOf P).index = 3 := by
  have h1 := Subgroup.card_mul_index ((zpowers y ⊔ zpowers b).subgroupOf P)
  have h2 : Nat.card ((zpowers y ⊔ zpowers b).subgroupOf P) = 3 ^ (2 * e + 1) := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv
  rw [h2, hP] at h1
  have h3 : 3 ^ (2 * e + 2) = 3 ^ (2 * e + 1) * 3 := by
    rw [show 2 * e + 2 = 2 * e + 1 + 1 by ring, pow_succ]
  rw [h3] at h1
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (by norm_num) _) h1

private lemma r891_normal_sup_zpowers {G : Type} [Group G] {P : Subgroup G} {y b : G} {e : ℕ}
    (hidx : ((zpowers y ⊔ zpowers b).subgroupOf P).index = 3)
    (hP : Nat.card P = 3 ^ (2 * e + 2)) :
    ((zpowers y ⊔ zpowers b).subgroupOf P).Normal := by
  refine Subgroup.normal_of_index_eq_minFac_card ?_
  rw [hidx, hP, Nat.Prime.pow_minFac Nat.prime_three (by omega)]

private lemma r891_comm_sup_zpowers {G : Type} [Group G] {y b : G} (hyb : Commute y b) :
    ∀ a ∈ zpowers y ⊔ zpowers b, ∀ c ∈ zpowers y ⊔ zpowers b, a * c = c * a := by
  intro a ha c hc
  exact @Subgroup.mul_comm_of_mem_isMulCommutative G _ _
    (r891_isMulCommutative_sup_zpowers hyb) a c ha hc

private lemma r891_exists_zpow_mul_of_mem {G : Type} [Group G] {y b z : G} (hyb : Commute y b)
    (hz : z ∈ zpowers y ⊔ zpowers b) : ∃ i j : ℤ, y ^ i * b ^ j = z :=
  (CFSG.GH74.GLS.Stage1.Thm3.Sec8.G2Syl.QPShape.mem_zpowers_sup_iff hyb).mp hz

private lemma r891_zpow_mul_eq_one {G : Type} [Group G] {y b : G}
    (hdisj : zpowers y ⊓ zpowers b = ⊥) {i j : ℤ} (h : y ^ i * b ^ j = 1) :
    y ^ i = 1 ∧ b ^ j = 1 :=
  Subgroup.disjoint_iff_mul_eq_one.mp (disjoint_iff.mpr hdisj)
    (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) i)
    (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) j) h

private lemma r891_pow_three_pow {G : Type} [Group G] (y : G) {e : ℕ} (he : 1 ≤ e) :
    (y ^ 3 ^ (e - 1)) ^ 3 = y ^ 3 ^ e := by
  rw [← pow_mul, show 3 ^ (e - 1) * 3 = 3 ^ e by rw [← pow_succ]; congr 1; omega]

private lemma r891_orderOf_pow_three {G : Type} [Group G] [Finite G] {b : G} {e : ℕ}
    (he : 1 ≤ e) (hb : orderOf b = 3 ^ e) : orderOf (b ^ 3 ^ (e - 1)) = 3 := by
  have h3e : 3 ^ (e - 1) * 3 = 3 ^ e := by
    rw [← pow_succ]
    congr 1
    omega
  rw [orderOf_pow, hb, Nat.gcd_eq_right (Nat.pow_dvd_pow 3 (by omega : e - 1 ≤ e))]
  rw [← h3e, Nat.mul_div_right 3 (pow_pos (by norm_num) (e - 1))]

private lemma r891_conj_mem_sup_zpowers {G : Type} [Group G] {P : Subgroup G} {y b : G}
    (hAle : zpowers y ⊔ zpowers b ≤ P)
    (hAn : ((zpowers y ⊔ zpowers b).subgroupOf P).Normal) {x a : G} (hx : x ∈ P)
    (ha : a ∈ zpowers y ⊔ zpowers b) : x * a * x⁻¹ ∈ zpowers y ⊔ zpowers b := by
  have := hAn
  have hPnorm : P ≤ Subgroup.normalizer (↑(zpowers y ⊔ zpowers b) : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hAle
  exact (Subgroup.mem_normalizer_iff.mp (hPnorm hx) a).mp ha

private lemma r891_orderOf_pow_e {G : Type} [Group G] {y : G} {e : ℕ}
    (hy : orderOf y = 3 ^ (e + 1)) : orderOf (y ^ 3 ^ e) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [← pow_mul, show 3 ^ e * 3 = 3 ^ (e + 1) by ring, ← hy, pow_orderOf_eq_one]
  · intro h1
    have hdvd : orderOf y ∣ 3 ^ e := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hy] at hdvd
    have hle : 3 ^ (e + 1) ≤ 3 ^ e := Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd
    have hlt : 3 ^ e < 3 ^ (e + 1) := by
      rw [pow_succ]
      nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) e]
    omega

private lemma r891_conj_pow_eq_zpow {G : Type} [Group G] {P : Subgroup G} {y b : G} {e : ℕ}
    (hyb : Commute y b) (hb : orderOf b = 3 ^ e)
    (hAle : zpowers y ⊔ zpowers b ≤ P)
    (hAn : ((zpowers y ⊔ zpowers b).subgroupOf P).Normal) :
    ∀ x ∈ P, ∃ i : ℤ, x * (y ^ 3 ^ e) * x⁻¹ = (y ^ 3 ^ e) ^ i := by
  have hyA : y ∈ zpowers y ⊔ zpowers b := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  intro x hx
  obtain ⟨i, j, hij⟩ :=
    r891_exists_zpow_mul_of_mem hyb (r891_conj_mem_sup_zpowers hAle hAn hx hyA)
  refine ⟨i, ?_⟩
  have h1 : x * (y ^ 3 ^ e) * x⁻¹ = (x * y * x⁻¹) ^ 3 ^ e := by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  have hb3 : b ^ 3 ^ e = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb] at this
  have hbj : b ^ (((3 ^ e : ℕ) : ℤ) * j) = 1 := by
    rw [zpow_mul, zpow_natCast, hb3, one_zpow]
  rw [h1, ← hij, r891_zpow_mul_pow hyb i j (3 ^ e), hbj, mul_one, zpow_mul, zpow_natCast]

private lemma r891_normal_zpowers_of_conj_eq_zpow {G : Type} [Group G] {P : Subgroup G} {y₀ : G}
    (hconj : ∀ x ∈ P, ∃ i : ℤ, x * y₀ * x⁻¹ = y₀ ^ i) :
    ((zpowers y₀).subgroupOf P).Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hn)
  obtain ⟨i, hi⟩ := hconj (g : G) g.2
  have h1 : ((g : G) * (n : G) * (g : G)⁻¹) = MulAut.conj (g : G) (y₀ ^ k) := by
    rw [MulAut.conj_apply, hk]
  rw [Subgroup.mem_subgroupOf]
  have h2 : ((g * n * g⁻¹ : ↥P) : G) = (g : G) * (n : G) * (g : G)⁻¹ := rfl
  rw [h2, h1, map_zpow, MulAut.conj_apply, hi, ← zpow_mul]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y₀) _

private lemma r891_pow_mem_zOf {G : Type} [Group G] [Finite G] {P : Subgroup G} {y : G} {e : ℕ}
    (hy : orderOf y = 3 ^ (e + 1)) (hP : Nat.card P = 3 ^ (2 * e + 2))
    (hy₀P : y ^ 3 ^ e ∈ P) (hnormal : ((zpowers (y ^ 3 ^ e)).subgroupOf P).Normal) :
    y ^ 3 ^ e ∈ ZOf P := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcenter : (zpowers (y ^ 3 ^ e)).subgroupOf P ≤ Subgroup.center ↥P := by
    refine normal_card_three_le_center_of_isPGroup_three ?_ hnormal ?_
    · exact IsPGroup.of_card (n := 2 * e + 2) hP
    · rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hy₀P)).toEquiv,
        Nat.card_zpowers, r891_orderOf_pow_e hy]
  have hmem : (⟨y ^ 3 ^ e, hy₀P⟩ : ↥P) ∈ Subgroup.center ↥P :=
    hcenter (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _))
  rw [ZOf, Subgroup.mem_inf]
  refine ⟨hy₀P, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem ⟨x, hx⟩)

private lemma r891_conj_eq_of_mem_zOf {G : Type} [Group G] {P : Subgroup G} {y₀ : G}
    (hy₀Z : y₀ ∈ ZOf P) {x : G} (hx : x ∈ P) : MulAut.conj x y₀ = y₀ := by
  rw [MulAut.conj_apply]
  have hc : x * y₀ = y₀ * x :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy₀Z).2 x hx
  rw [hc]
  group

private lemma r891_zOf_le_sup_zpowers {G : Type} [Group G] {P : Subgroup G} {y b b₁ : G}
    (hAle : zpowers y ⊔ zpowers b ≤ P)
    (hidx : ((zpowers y ⊔ zpowers b).subgroupOf P).index = 3)
    (hcomm : ∀ a ∈ zpowers y ⊔ zpowers b, ∀ c ∈ zpowers y ⊔ zpowers b, a * c = c * a)
    (hb₁A : b₁ ∈ zpowers y ⊔ zpowers b) (hb₁P : b₁ ∈ P) (hbZ : b₁ ∉ ZOf P) :
    ZOf P ≤ zpowers y ⊔ zpowers b := by
  intro z hz
  obtain ⟨hzP, hzC⟩ := Subgroup.mem_inf.mp hz
  by_contra hzA
  have hzp : (zpowers z).subgroupOf P = zpowers (⟨z, hzP⟩ : ↥P) := by
    ext u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by ext; exact hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk]; rfl⟩
  have hcoatom : IsCoatom ((zpowers y ⊔ zpowers b).subgroupOf P) :=
    Subgroup.isCoatom_of_index_prime (by rw [hidx]; exact Nat.prime_three)
  rcases (hcoatom.le_iff.mp
    (le_sup_left : (zpowers y ⊔ zpowers b).subgroupOf P ≤
      (zpowers y ⊔ zpowers b).subgroupOf P ⊔ (zpowers z).subgroupOf P)).symm with h | h
  · have hmem : (⟨z, hzP⟩ : ↥P) ∈
        (zpowers y ⊔ zpowers b).subgroupOf P ⊔ (zpowers z).subgroupOf P :=
      Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers z))
    rw [h] at hmem
    exact hzA (Subgroup.mem_subgroupOf.mp hmem)
  · have hsup : (zpowers y ⊔ zpowers b).subgroupOf P ⊔ zpowers (⟨z, hzP⟩ : ↥P) = ⊤ := by
      rw [← hzp]
      exact h
    have hT : ∀ a ∈ (zpowers y ⊔ zpowers b).subgroupOf P,
        ∀ c ∈ (zpowers y ⊔ zpowers b).subgroupOf P, Commute a c := by
      intro a ha c hc
      have ha' : (a : G) ∈ zpowers y ⊔ zpowers b := Subgroup.mem_subgroupOf.mp ha
      have hc' : (c : G) ∈ zpowers y ⊔ zpowers b := Subgroup.mem_subgroupOf.mp hc
      exact Subtype.ext (hcomm (a : G) ha' (c : G) hc')
    have hd : ∀ a ∈ (zpowers y ⊔ zpowers b).subgroupOf P, Commute a (⟨z, hzP⟩ : ↥P) := by
      intro a ha
      have ha' : (a : G) ∈ zpowers y ⊔ zpowers b := Subgroup.mem_subgroupOf.mp ha
      have hza : (a : G) * z = z * (a : G) :=
        Subgroup.mem_centralizer_iff.mp hzC (a : G) (hAle ha')
      have : (a : ↥P) * ⟨z, hzP⟩ = ⟨z, hzP⟩ * (a : ↥P) := by ext; exact hza
      exact this
    have hcentral := r891_central_of_sup_zpowers (T := (zpowers y ⊔ zpowers b).subgroupOf P)
      (d := ⟨z, hzP⟩) hT hd hsup
      (show (⟨b₁, hb₁P⟩ : ↥P) ∈ (zpowers y ⊔ zpowers b).subgroupOf P from hb₁A)
    refine hbZ ?_
    rw [ZOf, Subgroup.mem_inf]
    refine ⟨hb₁P, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hcentral ⟨w, hw⟩)

private lemma r891_pow_three_mem_sup {G : Type} [Group G] [Finite G] {P : Subgroup G} {y b : G}
    (hidx : ((zpowers y ⊔ zpowers b).subgroupOf P).index = 3)
    (hAn : ((zpowers y ⊔ zpowers b).subgroupOf P).Normal) {x : G} (hx : x ∈ P) :
    x ^ 3 ∈ zpowers y ⊔ zpowers b := by
  have := hAn
  have hcard : Nat.card (↥P ⧸ ((zpowers y ⊔ zpowers b).subgroupOf P)) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have : Fintype (↥P ⧸ ((zpowers y ⊔ zpowers b).subgroupOf P)) := Fintype.ofFinite _
  have hmem : (⟨x, hx⟩ : ↥P) ^ 3 ∈ (zpowers y ⊔ zpowers b).subgroupOf P := by
    have h1 : QuotientGroup.mk (s := (zpowers y ⊔ zpowers b).subgroupOf P)
        ((⟨x, hx⟩ : ↥P) ^ 3) = 1 := by
      rw [QuotientGroup.mk_pow, ← hcard, Nat.card_eq_fintype_card]
      exact pow_card_eq_one
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact Subgroup.mem_subgroupOf.mp hmem

private lemma r891_order_three_mem_sup {G : Type} [Group G] {y b : G} {e : ℕ} (he : 1 ≤ e)
    (hy : orderOf y = 3 ^ (e + 1)) (hb : orderOf b = 3 ^ e) (hyb : Commute y b)
    (hdisj : zpowers y ⊓ zpowers b = ⊥) :
    ∀ a ∈ zpowers y ⊔ zpowers b, a ^ 3 = 1 →
      ∃ u v : ℤ, a = (y ^ 3 ^ e) ^ u * (b ^ 3 ^ (e - 1)) ^ v := by
  intro a ha ha3
  obtain ⟨i, j, hij⟩ := r891_exists_zpow_mul_of_mem hyb ha
  have h3 : (y ^ i * b ^ j) ^ 3 = 1 := by rw [hij, ha3]
  rw [r891_zpow_mul_pow hyb i j 3] at h3
  obtain ⟨hy3, hb3⟩ := r891_zpow_mul_eq_one hdisj h3
  have hdi : ((3 : ℤ) ^ e) ∣ i :=
    r891_dvd_of_zpow_eq_one (k := 1) (by rw [hy]) (by simpa using hy3)
  have hdj : ((3 : ℤ) ^ (e - 1)) ∣ j := by
    have h := r891_dvd_of_zpow_eq_one (y := b) (e := e - 1) (k := 1)
      (by rw [hb]; congr 1; omega) (by simpa using hb3)
    simpa using h
  obtain ⟨u, hu⟩ := hdi
  obtain ⟨v, hv⟩ := hdj
  refine ⟨u, v, ?_⟩
  have hu' : i = ((3 ^ e : ℕ) : ℤ) * u := by rw [hu]; push_cast; ring
  have hv' : j = ((3 ^ (e - 1) : ℕ) : ℤ) * v := by rw [hv]; push_cast; ring
  rw [← hij, hu', hv', zpow_mul, zpow_mul]
  simp only [zpow_natCast]

private lemma r891_conj_mem_zpowers_mul {G : Type} [Group G] {P : Subgroup G} {y b y₀ b₁ : G}
    (hAle : zpowers y ⊔ zpowers b ≤ P)
    (hAn : ((zpowers y ⊔ zpowers b).subgroupOf P).Normal)
    (hcomm : ∀ a ∈ zpowers y ⊔ zpowers b, ∀ c ∈ zpowers y ⊔ zpowers b, a * c = c * a)
    (hy₀A : y₀ ∈ zpowers y ⊔ zpowers b) (hb₁A : b₁ ∈ zpowers y ⊔ zpowers b)
    (hb₁ord : orderOf b₁ = 3) (hx3A : ∀ x ∈ P, x ^ 3 ∈ zpowers y ⊔ zpowers b)
    (horder3 : ∀ a ∈ zpowers y ⊔ zpowers b, a ^ 3 = 1 → ∃ u v : ℤ, a = y₀ ^ u * b₁ ^ v)
    (hfix_y₀ : ∀ x ∈ P, MulAut.conj x y₀ = y₀) :
    ∀ x ∈ P, ∃ s : ℤ, MulAut.conj x b₁ = y₀ ^ s * b₁ := by
  have hb₁cube : b₁ ^ 3 = 1 := by
    rw [← hb₁ord]
    exact pow_orderOf_eq_one _
  intro x hx
  have hmem : MulAut.conj x b₁ ∈ zpowers y ⊔ zpowers b := by
    rw [MulAut.conj_apply]
    exact r891_conj_mem_sup_zpowers hAle hAn hx hb₁A
  have hcube : (MulAut.conj x b₁) ^ 3 = 1 := by
    rw [← map_pow, hb₁cube, map_one]
  obtain ⟨u₀, v₀, huv⟩ := horder3 _ hmem hcube
  have hcommy : Commute y₀ b₁ := (hcomm y₀ hy₀A b₁ hb₁A : y₀ * b₁ = b₁ * y₀)
  have hφ3 : (MulAut.conj x ^ 3) b₁ = b₁ := by
    rw [← map_pow, MulAut.conj_apply]
    have h3A : x ^ 3 ∈ zpowers y ⊔ zpowers b := hx3A x hx
    have hc : x ^ 3 * b₁ = b₁ * x ^ 3 := hcomm _ h3A _ hb₁A
    rw [hc]
    group
  have hcalc := r891_conj_three (MulAut.conj x) (y₀ := y₀) (b₁ := b₁) (u := u₀) (v := v₀)
    (hfix_y₀ x hx) huv hcommy
  have h1 : b₁ = y₀ ^ (u₀ * (1 + v₀ + v₀ ^ 2)) * b₁ ^ (v₀ ^ 3) :=
    hφ3.symm.trans hcalc
  have hBb : b₁ ^ (v₀ ^ 3) = y₀ ^ (-(u₀ * (1 + v₀ + v₀ ^ 2))) * b₁ := by
    calc b₁ ^ (v₀ ^ 3) = (y₀ ^ (u₀ * (1 + v₀ + v₀ ^ 2)))⁻¹ *
          (y₀ ^ (u₀ * (1 + v₀ + v₀ ^ 2)) * b₁ ^ (v₀ ^ 3)) := by group
      _ = (y₀ ^ (u₀ * (1 + v₀ + v₀ ^ 2)))⁻¹ * b₁ := by rw [← h1]
      _ = y₀ ^ (-(u₀ * (1 + v₀ + v₀ ^ 2))) * b₁ := by rw [← zpow_neg]
  have h2 : b₁ ^ (v₀ ^ 3 - 1) = y₀ ^ (-(u₀ * (1 + v₀ + v₀ ^ 2))) := by
    have step : b₁ ^ (v₀ ^ 3 - 1) = b₁ ^ (v₀ ^ 3) * b₁⁻¹ := by
      rw [show v₀ ^ 3 - 1 = v₀ ^ 3 + (-1) by ring, zpow_add, zpow_neg_one]
    rw [step, hBb, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v₀ ^ 3 - v₀ = 3 * m := by
    have h : v₀ ^ 3 ≡ v₀ [ZMOD 3] := by
      have := (ZMod.intCast_eq_intCast_iff (v₀ ^ 3) v₀ 3).mp (by
        push_cast
        exact ZMod.pow_card (v₀ : ZMod 3))
      exact this
    obtain ⟨m, hm⟩ := Int.ModEq.dvd h
    exact ⟨-m, by omega⟩
  have hpow : b₁ ^ (v₀ ^ 3 - 1) = b₁ ^ (v₀ - 1) := by
    rw [show v₀ ^ 3 - 1 = (v₀ - 1) + 3 * m by rw [← hm]; ring, zpow_add]
    have h3m : b₁ ^ ((3 : ℤ) * m) = 1 := by
      rw [zpow_mul, show b₁ ^ (3 : ℤ) = 1 from by simpa using hb₁cube, one_zpow]
    rw [h3m, mul_one]
  have hsub : b₁ ^ (v₀ - 1) = y₀ ^ (-(u₀ * (1 + v₀ + v₀ ^ 2))) := by
    rw [← hpow, h2]
  refine ⟨u₀ + -(u₀ * (1 + v₀ + v₀ ^ 2)), ?_⟩
  rw [huv]
  calc y₀ ^ u₀ * b₁ ^ v₀ = y₀ ^ u₀ * (b₁ ^ (v₀ - 1) * b₁) := by
        conv_lhs => rw [show v₀ = (v₀ - 1) + 1 by ring]
        rw [zpow_add, zpow_one]
    _ = y₀ ^ u₀ * (y₀ ^ (-(u₀ * (1 + v₀ + v₀ ^ 2))) * b₁) := by rw [hsub]
    _ = y₀ ^ (u₀ + -(u₀ * (1 + v₀ + v₀ ^ 2))) * b₁ := by
        rw [← mul_assoc, ← zpow_add]

private lemma r891_exists_central_cube {G : Type} [Group G] {P : Subgroup G} {y₀ : G} {e : ℕ}
    (hP : Nat.card P = 3 ^ (2 * e + 2)) {z : G} (hzZ : z ∈ ZOf P)
    (hz0 : z ∉ zpowers y₀) :
    ∃ w ∈ ZOf P, w ∉ zpowers y₀ ∧ w ^ 3 ∈ zpowers y₀ := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 2 * e + 2) hP
  have hZ3 : IsPGroup 3 ↥(ZOf P) := hP3.to_le inf_le_left
  obtain ⟨r, hr⟩ := IsPGroup.exists_orderOf_eq_pow hZ3 ⟨z, hzZ⟩
  have hmemr : z ^ 3 ^ r ∈ zpowers y₀ := by
    have h1 : (⟨z, hzZ⟩ : ↥(ZOf P)) ^ 3 ^ r = 1 := by
      rw [← hr]
      exact pow_orderOf_eq_one _
    have h2 : z ^ 3 ^ r = 1 := by
      have := congrArg Subtype.val h1
      simpa using this
    rw [h2]
    exact Subgroup.one_mem _
  have hmem0 : ¬ z ^ 3 ^ 0 ∈ zpowers y₀ := by simpa using hz0
  have hex : ∃ j, z ^ 3 ^ j ∈ zpowers y₀ := ⟨r, hmemr⟩
  set j := Nat.find hex with hjdef
  have hjspec : z ^ 3 ^ j ∈ zpowers y₀ := Nat.find_spec hex
  have hjpos : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exact absurd (h ▸ hjspec) hmem0
    · exact h
  refine ⟨z ^ (((3 ^ (j - 1) : ℕ) : ℤ)), Subgroup.zpow_mem (ZOf P) hzZ _, ?_, ?_⟩
  · intro hw
    have hw' : z ^ 3 ^ (j - 1) ∈ zpowers y₀ := by
      rw [show z ^ 3 ^ (j - 1) = z ^ (((3 ^ (j - 1) : ℕ) : ℤ)) by rw [zpow_natCast]]
      exact hw
    exact Nat.find_min hex (show j - 1 < j by omega) hw'
  · have h3 : (z ^ (((3 ^ (j - 1) : ℕ) : ℤ))) ^ 3 = z ^ 3 ^ j := by
      rw [← zpow_natCast (a := z ^ (((3 ^ (j - 1) : ℕ) : ℤ))) (n := 3), ← zpow_mul,
        ← zpow_natCast (a := z) (n := 3 ^ j)]
      congr 1
      push_cast
      rw [← pow_succ]
      congr 1
      omega
    rw [h3]
    exact hjspec

private lemma r891_exists_form {G : Type} [Group G] {y b w : G} {e : ℕ} (he : 1 ≤ e)
    (hy : orderOf y = 3 ^ (e + 1)) (hb : orderOf b = 3 ^ e) (hyb : Commute y b)
    (hdisj : zpowers y ⊓ zpowers b = ⊥)
    (hwA : w ∈ zpowers y ⊔ zpowers b) (hw3 : w ^ 3 ∈ zpowers (y ^ 3 ^ e)) :
    ∃ a c : ℤ, w = (y ^ 3 ^ (e - 1)) ^ a * (b ^ 3 ^ (e - 1)) ^ c := by
  obtain ⟨i, j, hij⟩ := r891_exists_zpow_mul_of_mem hyb hwA
  obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp hw3
  have hw3' : y ^ ((3 : ℤ) * i) * b ^ ((3 : ℤ) * j) = y ^ ((3 : ℤ) ^ e * t) := by
    have h1 : (y ^ i * b ^ j) ^ 3 = y ^ ((3 : ℤ) * i) * b ^ ((3 : ℤ) * j) :=
      r891_zpow_mul_pow hyb i j 3
    calc y ^ ((3 : ℤ) * i) * b ^ ((3 : ℤ) * j) = (y ^ i * b ^ j) ^ 3 := h1.symm
      _ = w ^ 3 := by rw [hij]
      _ = (y ^ 3 ^ e) ^ t := ht.symm
      _ = (y ^ ((3 ^ e : ℕ) : ℤ)) ^ t := by rw [zpow_natCast]
      _ = y ^ (((3 ^ e : ℕ) : ℤ) * t) := (zpow_mul _ _ _).symm
      _ = y ^ ((3 : ℤ) ^ e * t) := by
          rw [show ((3 ^ e : ℕ) : ℤ) = (3 : ℤ) ^ e by push_cast; ring]
  have hkey : y ^ ((3 : ℤ) * i - (3 : ℤ) ^ e * t) * b ^ ((3 : ℤ) * j) = 1 := by
    have hsplit : y ^ ((3 : ℤ) * i - (3 : ℤ) ^ e * t) =
        y ^ ((3 : ℤ) * i) * y ^ (-((3 : ℤ) ^ e * t)) := by
      rw [← zpow_add]
      ring_nf
    calc y ^ ((3 : ℤ) * i - (3 : ℤ) ^ e * t) * b ^ ((3 : ℤ) * j)
        = (y ^ ((3 : ℤ) * i) * y ^ (-((3 : ℤ) ^ e * t))) *
            b ^ ((3 : ℤ) * j) := by rw [hsplit]
      _ = y ^ ((3 : ℤ) * i) *
            (y ^ (-((3 : ℤ) ^ e * t)) * b ^ ((3 : ℤ) * j)) := by rw [mul_assoc]
      _ = y ^ ((3 : ℤ) * i) *
            (b ^ ((3 : ℤ) * j) * y ^ (-((3 : ℤ) ^ e * t))) := by
          rw [(hyb.zpow_zpow _ _).eq]
      _ = (y ^ ((3 : ℤ) * i) * b ^ ((3 : ℤ) * j)) * y ^ (-((3 : ℤ) ^ e * t)) := by
          rw [mul_assoc]
      _ = y ^ ((3 : ℤ) ^ e * t) * y ^ (-((3 : ℤ) ^ e * t)) := by rw [hw3']
      _ = 1 := by rw [← zpow_add]; simp
  obtain ⟨hy3, hb3⟩ := r891_zpow_mul_eq_one hdisj hkey
  have hdi : ((3 : ℤ) ^ (e - 1)) ∣ i := by
    have h3eZ : ((3 : ℤ)) ^ e = 3 * (3 : ℤ) ^ (e - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : y ^ ((3 : ℤ) * (i - (3 : ℤ) ^ (e - 1) * t)) = 1 := by
      rw [show (3 : ℤ) * (i - (3 : ℤ) ^ (e - 1) * t) = 3 * i - (3 : ℤ) ^ e * t by
        rw [h3eZ]; ring]
      exact hy3
    have h := r891_dvd_of_zpow_eq_one (y := y) (e := e) (k := 1) hy (by simpa using h3)
    have hdvd1 : ((3 : ℤ) ^ (e - 1)) ∣ (3 : ℤ) ^ e := by
      rw [show e = e - 1 + 1 by omega, pow_succ]
      exact dvd_mul_right _ _
    have h4 : ((3 : ℤ) ^ (e - 1)) ∣ i - (3 : ℤ) ^ (e - 1) * t := dvd_trans hdvd1 h
    have h5 : ((3 : ℤ) ^ (e - 1)) ∣ (3 : ℤ) ^ (e - 1) * t := Dvd.intro t (by ring)
    have h6 := dvd_add h4 h5
    convert h6 using 2
    ring
  have hdj : ((3 : ℤ) ^ (e - 1)) ∣ j := by
    have hb' : orderOf b = 3 ^ ((e - 1) + 1) := by rw [hb]; congr 1; omega
    have h := r891_dvd_of_zpow_eq_one (y := b) (e := e - 1) (k := 1) hb'
      (by simpa using hb3)
    simpa using h
  obtain ⟨a, ha⟩ := hdi
  obtain ⟨c, hc⟩ := hdj
  refine ⟨a, c, ?_⟩
  have ha' : i = ((3 ^ (e - 1) : ℕ) : ℤ) * a := by rw [ha]; push_cast; ring
  have hc' : j = ((3 ^ (e - 1) : ℕ) : ℤ) * c := by rw [hc]; push_cast; ring
  rw [← hij, ha', hc', zpow_mul, zpow_mul]
  simp only [zpow_natCast]

private lemma r891_dvd_case {G : Type} [Group G] {P : Subgroup G} {y₀ y₁ b₁ w : G}
    (hcube_y₁ : y₁ ^ (3 : ℤ) = y₀) (hb₁cube : b₁ ^ 3 = 1) (hcommy : Commute y₀ b₁)
    (hwZ : w ∈ ZOf P) (hw0 : w ∉ zpowers y₀) (hzy₀ : zpowers y₀ ≤ ZOf P)
    {a c : ℤ} (h3a : (3 : ℤ) ∣ a) (hwform : w = y₁ ^ a * b₁ ^ c) :
    b₁ ∈ ZOf P := by
  have hcube_b₁ : b₁ ^ (3 : ℤ) = 1 := by simpa using hb₁cube
  obtain ⟨a', ha'⟩ := h3a
  have hwc : w = y₀ ^ a' * b₁ ^ c := by
    rw [hwform, ha']
    congr 1
    rw [zpow_mul, hcube_y₁]
  have hbcZ : b₁ ^ c ∈ ZOf P := by
    have h1 : w * (y₀ ^ a')⁻¹ ∈ ZOf P :=
      Subgroup.mul_mem _ hwZ
        (Subgroup.inv_mem _ (hzy₀ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y₀) a')))
    convert h1 using 1
    rw [hwc, (hcommy.zpow_zpow a' c).eq, mul_assoc, mul_inv_cancel, mul_one]
  by_cases hc1 : b₁ ^ c = 1
  · exfalso
    exact hw0 (by rw [hwc, hc1, mul_one]
                  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers y₀) a')
  · have hem : b₁ ^ c = b₁ ^ (c % 3) := zpow_eq_zpow_emod c hcube_b₁
    have hc0 : 0 ≤ c % 3 := Int.emod_nonneg c (by norm_num)
    have hc3 : c % 3 < 3 := Int.emod_lt_of_pos c (by norm_num)
    have hmem : b₁ ∈ Subgroup.zpowers (b₁ ^ c) := by
      interval_cases h : c % 3
      · exact absurd (by rw [hem, zpow_zero]) hc1
      · rw [hem, zpow_one]
        exact Subgroup.mem_zpowers b₁
      · rw [hem]
        refine Subgroup.mem_zpowers_iff.mpr ⟨2, ?_⟩
        rw [← zpow_mul, show (2 : ℤ) * 2 = 1 + 3 by norm_num, zpow_add, hcube_b₁,
          mul_one, zpow_one]
    exact Subgroup.zpowers_le.mpr hbcZ hmem

private lemma r891_not_dvd_case {G : Type} [Group G] {P : Subgroup G} {y₀ y₁ b₁ w : G}
    (hy₀_eq : y₁ ^ 3 = y₀) (hcommy : Commute y₀ b₁)
    (hfixw : ∀ x ∈ P, MulAut.conj x w = w)
    (hfix_y₀ : ∀ x ∈ P, MulAut.conj x y₀ = y₀)
    (hb1_conj : ∀ x ∈ P, ∃ s : ℤ, MulAut.conj x b₁ = y₀ ^ s * b₁)
    {a c : ℤ} (hwform : w = y₁ ^ a * b₁ ^ c) (ha3 : ¬ (3 : ℤ) ∣ a) :
    ∀ x ∈ P, MulAut.conj x y₁ ∈ Subgroup.zpowers y₁ := by
  have hy₀_mem_y₁ : y₀ ∈ Subgroup.zpowers y₁ := by
    rw [← hy₀_eq]
    simp
  have ha_dec : a = 3 * (a / 3) + a % 3 := by
    have h := Int.emod_add_mul_ediv a 3
    linarith
  have hr : a % 3 = 1 ∨ a % 3 = 2 := by
    have h0 : 0 ≤ a % 3 := Int.emod_nonneg a (by norm_num)
    have h3 : a % 3 < 3 := Int.emod_lt_of_pos a (by norm_num)
    omega
  intro x hx
  obtain ⟨s, hs⟩ := hb1_conj x hx
  have hφa : (MulAut.conj x y₁) ^ a ∈ Subgroup.zpowers y₁ := by
    have h1 : (MulAut.conj x y₁) ^ a = w * ((y₀ ^ s * b₁) ^ c)⁻¹ := by
      have h2 : MulAut.conj x w =
          (MulAut.conj x y₁) ^ a * (MulAut.conj x b₁) ^ c := by
        rw [hwform, map_mul, map_zpow, map_zpow]
      rw [hfixw x hx, hs] at h2
      rw [h2]
      group
    have h3 : (y₀ ^ s * b₁) ^ c = y₀ ^ (s * c) * b₁ ^ c := by
      rw [Commute.mul_zpow (hcommy.zpow_left s) c, ← zpow_mul]
    rw [h1, h3, hwform]
    have h4 : (y₁ ^ a * b₁ ^ c) * (y₀ ^ (s * c) * b₁ ^ c)⁻¹ =
        y₁ ^ a * (y₀ ^ (s * c))⁻¹ := by group
    rw [h4]
    refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y₁) a)
      (Subgroup.inv_mem _ ?_)
    exact Subgroup.zpow_mem _ hy₀_mem_y₁ _
  have hφ3 : (MulAut.conj x y₁) ^ 3 = y₀ := by
    rw [← map_pow, hy₀_eq, hfix_y₀ x hx]
  have hφ3z : (MulAut.conj x y₁) ^ (3 : ℤ) = y₀ := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
    exact hφ3
  have hsplit : (MulAut.conj x y₁) ^ a =
      ((MulAut.conj x y₁) ^ (3 : ℤ)) ^ (a / 3) * (MulAut.conj x y₁) ^ (a % 3) := by
    conv_lhs => rw [ha_dec]
    rw [zpow_add, zpow_mul]
  have h7 : ((MulAut.conj x y₁) ^ (3 : ℤ)) ^ (a / 3) ∈ Subgroup.zpowers y₁ := by
    rw [hφ3z]
    exact Subgroup.zpow_mem _ hy₀_mem_y₁ _
  have hrem : (MulAut.conj x y₁) ^ (a % 3) ∈ Subgroup.zpowers y₁ := by
    have h8 : (MulAut.conj x y₁) ^ (a % 3) =
        (((MulAut.conj x y₁) ^ (3 : ℤ)) ^ (a / 3))⁻¹ * (MulAut.conj x y₁) ^ a := by
      rw [hsplit]
      group
    rw [h8]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h7) hφa
  rcases hr with h | h
  · simpa [h] using hrem
  · have h2 : MulAut.conj x y₁ =
        ((MulAut.conj x y₁) ^ 2) ^ 2 * ((MulAut.conj x y₁) ^ 3)⁻¹ := by
      group
    have h3g : (MulAut.conj x y₁) ^ 3 ∈ Subgroup.zpowers y₁ := by
      rw [hφ3]
      exact hy₀_mem_y₁
    have h2g : (MulAut.conj x y₁) ^ 2 ∈ Subgroup.zpowers y₁ := by
      simpa [h] using hrem
    rw [h2]
    exact Subgroup.mul_mem (Subgroup.zpowers y₁)
      (Subgroup.pow_mem (Subgroup.zpowers y₁) h2g 2)
      (Subgroup.inv_mem (Subgroup.zpowers y₁) h3g)

theorem zOf_eq_zpowers_of_index_three {G : Type} [Group G] [Finite G] {P : Subgroup G}
    {y b : G} {e : ℕ} (he : 1 ≤ e) (hyP : y ∈ P) (hbP : b ∈ P) (hy : orderOf y = 3 ^ (e + 1))
    (hb : orderOf b = 3 ^ e) (hyb : Commute y b) (hdisj : zpowers y ⊓ zpowers b = ⊥)
    (hP : Nat.card P = 3 ^ (2 * e + 2)) (hbZ : b ^ 3 ^ (e - 1) ∉ ZOf P)
    (hyN : ∃ x ∈ P, x * y ^ 3 ^ (e - 1) * x⁻¹ ∉ zpowers (y ^ 3 ^ (e - 1))) :
    ZOf P = zpowers (y ^ 3 ^ e) := by
  classical
  have hAle : zpowers y ⊔ zpowers b ≤ P :=
    sup_le (Subgroup.zpowers_le.mpr hyP) (Subgroup.zpowers_le.mpr hbP)
  have hidx : ((zpowers y ⊔ zpowers b).subgroupOf P).index = 3 :=
    r891_index_sup_zpowers hAle (r891_card_sup_zpowers hy hb hyb hdisj) hP
  have hAn : ((zpowers y ⊔ zpowers b).subgroupOf P).Normal :=
    r891_normal_sup_zpowers hidx hP
  have hcomm := r891_comm_sup_zpowers hyb
  have hyA : y ∈ zpowers y ⊔ zpowers b := Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hy₀A : y ^ 3 ^ e ∈ zpowers y ⊔ zpowers b :=
    Subgroup.mem_sup_left
      (by simp)
  have hb₁A : b ^ 3 ^ (e - 1) ∈ zpowers y ⊔ zpowers b :=
    Subgroup.mem_sup_right
      (by simp)
  have hy₀P : y ^ 3 ^ e ∈ P := hAle hy₀A
  have hb₁P : b ^ 3 ^ (e - 1) ∈ P := hAle hb₁A
  have hy₀_eq : (y ^ 3 ^ (e - 1)) ^ 3 = y ^ 3 ^ e := r891_pow_three_pow y he
  have hb₁cube : (b ^ 3 ^ (e - 1)) ^ 3 = 1 := by
    have hb3 : b ^ 3 ^ e = 1 := by
      have := pow_orderOf_eq_one b
      rwa [hb] at this
    rw [r891_pow_three_pow b he, hb3]
  have hb₁ord : orderOf (b ^ 3 ^ (e - 1)) = 3 := r891_orderOf_pow_three he hb
  have hy₀Z : y ^ 3 ^ e ∈ ZOf P :=
    r891_pow_mem_zOf hy hP hy₀P
      (r891_normal_zpowers_of_conj_eq_zpow (r891_conj_pow_eq_zpow hyb hb hAle hAn))
  have hfix_y₀ : ∀ x ∈ P, MulAut.conj x (y ^ 3 ^ e) = y ^ 3 ^ e :=
    fun x hx => r891_conj_eq_of_mem_zOf hy₀Z hx
  have horder3 : ∀ a ∈ zpowers y ⊔ zpowers b, a ^ 3 = 1 →
      ∃ u v : ℤ, a = (y ^ 3 ^ e) ^ u * (b ^ 3 ^ (e - 1)) ^ v :=
    r891_order_three_mem_sup he hy hb hyb hdisj
  have hx3A : ∀ x ∈ P, x ^ 3 ∈ zpowers y ⊔ zpowers b :=
    fun x hx => r891_pow_three_mem_sup hidx hAn hx
  have hb1_conj : ∀ x ∈ P, ∃ s : ℤ, MulAut.conj x (b ^ 3 ^ (e - 1)) =
      (y ^ 3 ^ e) ^ s * (b ^ 3 ^ (e - 1)) :=
    r891_conj_mem_zpowers_mul hAle hAn hcomm hy₀A hb₁A hb₁ord hx3A horder3 hfix_y₀
  have hZleA : ZOf P ≤ zpowers y ⊔ zpowers b :=
    r891_zOf_le_sup_zpowers hAle hidx hcomm hb₁A hb₁P hbZ
  refine le_antisymm ?_ (Subgroup.zpowers_le.mpr hy₀Z)
  by_contra hle
  obtain ⟨z, hzZ, hz0⟩ : ∃ z ∈ ZOf P, z ∉ Subgroup.zpowers (y ^ 3 ^ e) := by
    by_contra h
    push Not at h
    exact hle h
  obtain ⟨w, hwZ, hw0, hw3⟩ := r891_exists_central_cube hP hzZ hz0
  have hwA : w ∈ zpowers y ⊔ zpowers b := hZleA hwZ
  obtain ⟨a, c, hwform⟩ := r891_exists_form he hy hb hyb hdisj hwA hw3
  have hcommy : Commute (y ^ 3 ^ e) (b ^ 3 ^ (e - 1)) := hcomm _ hy₀A _ hb₁A
  have hcube_y₁ : (y ^ 3 ^ (e - 1)) ^ (3 : ℤ) = y ^ 3 ^ e := by simpa using hy₀_eq
  have hfixw : ∀ x ∈ P, MulAut.conj x w = w :=
    fun x hx => r891_conj_eq_of_mem_zOf hwZ hx
  by_cases h3a : (3 : ℤ) ∣ a
  · exact hbZ (r891_dvd_case hcube_y₁ hb₁cube hcommy hwZ hw0
      (Subgroup.zpowers_le.mpr hy₀Z) h3a hwform)
  · obtain ⟨x₀, hx₀P, hx₀N⟩ := hyN
    have hmem : MulAut.conj x₀ (y ^ 3 ^ (e - 1)) ∈ Subgroup.zpowers (y ^ 3 ^ (e - 1)) :=
      r891_not_dvd_case hy₀_eq hcommy hfixw hfix_y₀ hb1_conj hwform h3a x₀ hx₀P
    exact hx₀N (by rw [← MulAut.conj_apply]; exact hmem)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

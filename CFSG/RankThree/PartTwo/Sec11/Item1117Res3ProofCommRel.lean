module

import CFSG.RankThree.PartTwo.Sec11.Item1117ProofField
public import CFSG.RankThree.PartTwo.Sec11.Item1119Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item1117Res3Proof

section Arith

theorem not_dvd_of_cube_eq_one {k : ℤ} (h1 : (9 : ℤ) ∣ k ^ 3 - 1) (h2 : (9 : ℤ) ∣ 1 + k + k ^ 2) :
    False := by
  have e1 : ((k : ZMod 9)) ^ 3 - 1 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (k ^ 3 - 1) 9).mpr h1
    push_cast at this
    exact this
  have e2 : 1 + (k : ZMod 9) + (k : ZMod 9) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (1 + k + k ^ 2) 9).mpr h2
    push_cast at this
    exact this
  generalize (k : ZMod 9) = t at e1 e2
  revert t
  decide

theorem inv_mul_zpow_mul {G : Type*} [Group G] (g y : G) (m : ℤ) :
    g⁻¹ * y ^ m * g = (g⁻¹ * y * g) ^ m := by
  have e := map_zpow (MulAut.conj g⁻¹) y m
  simp only [MulAut.conj_apply, inv_inv] at e
  exact e

theorem inv_mul_pow_mul {G : Type*} [Group G] (g y : G) (m : ℕ) :
    g⁻¹ * y ^ m * g = (g⁻¹ * y * g) ^ m := by
  have e := map_pow (MulAut.conj g⁻¹) y m
  simp only [MulAut.conj_apply, inv_inv] at e
  exact e

end Arith

section Data


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem twentySeven_dvd_orderOf_x (h : Sec11Data G A c L a R Y d x s r g) (hx : 9 < orderOf x) :
    27 ∣ orderOf x := by
  obtain ⟨k, hk⟩ := Item1117Proof.x_pow_eq_one h
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hj] at hx ⊢
  have hj3 : 3 ≤ j := by
    by_contra hlt
    push Not at hlt
    interval_cases j <;> norm_num at hx
  exact (Nat.pow_dvd_pow 3 hj3 : 3 ^ 3 ∣ 3 ^ j)

theorem step1119Comm_concl_of_relations (hbig : Sec11Big G A c L a R Y d x s r g)
    (h1 : x ^ 3 * (g⁻¹ * x ^ 3 * g) = (g⁻¹ * x ^ 3 * g) * x ^ 3)
    (h2 : x ^ 3 * (g⁻¹ * x ^ 3 * g) * (g⁻¹ * (g⁻¹ * x ^ 3 * g) * g) = 1)
    (h3 : ∀ z ∈ sec11P R g ⊓ Y, z * x ^ 3 = x ^ 3 * z → z * g = g * z →
      z ∈ Subgroup.zpowers d) :
    ∃ v : G, v ∉ Subgroup.closure ({x ^ 9, v ^ 3} : Set G) ∧
      g ∈ Subgroup.normalizer ((Subgroup.closure {x ^ 9, v ^ 3} : Subgroup G) : Set G) ∧
      (∀ z ∈ sec11P R g ⊓ Y, (∀ w ∈ sec11P R g ⊓ Y, z * w = w * z) →
        z ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G)) ∧
      ∃ w ∈ Subgroup.closure ({x ^ 9, v ^ 3} : Set G), (x ^ 3)⁻¹ * g⁻¹ * x ^ 3 * g = v * w := by
  have h := hbig.toSec11Data
  set y := x ^ 3 with hy
  set y' := g⁻¹ * y * g with hy'
  set v := y⁻¹ * y' with hv
  have hx9 : x ^ 9 = y ^ 3 := by rw [hy, ← pow_mul]
  have hg3 : g ^ 3 = 1 := by rw [← hbig.orderOf_g, pow_orderOf_eq_one]
  have hyy' : Commute y y' := h1
  have hyv : Commute y v := ((Commute.refl y).inv_right).mul_right hyy'
  have hy'v : y' = y * v := by rw [hv, mul_inv_cancel_left]
  have hy''inv : g⁻¹ * y' * g = (y * y')⁻¹ := eq_inv_of_mul_eq_one_right h2
  have h27 := twentySeven_dvd_orderOf_x h hbig.orderOf_x_gt
  have hy9 : ∀ k : ℤ, y ^ k = 1 → (9 : ℤ) ∣ k := by
    intro k hk
    have h1' : x ^ (3 * k) = 1 := by rw [zpow_mul]; exact_mod_cast hk
    have h2' : (orderOf x : ℤ) ∣ 3 * k := orderOf_dvd_iff_zpow_eq_one.mpr h1'
    obtain ⟨m, hm⟩ := h27
    rw [hm] at h2'
    push_cast at h2'
    obtain ⟨t, ht⟩ := h2'
    exact ⟨m * t, by linarith⟩
  have hP3 := h.isPGroup_sec11P
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hyP : y ∈ sec11P R g := (sec11P R g).pow_mem hxP 3
  have hy'P : y' ∈ sec11P R g :=
    (sec11P R g).mul_mem ((sec11P R g).mul_mem ((sec11P R g).inv_mem hgP) hyP) hgP
  have hvP : v ∈ sec11P R g := (sec11P R g).mul_mem ((sec11P R g).inv_mem hyP) hy'P
  set N := Subgroup.closure ({x ^ 9, v ^ 3} : Set G) with hN
  have hcube : ∀ w ∈ Subgroup.closure ({y, v} : Set G), w ^ 3 ∈ N := by
    intro w hw
    obtain ⟨i, j, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hyv.eq hw
    rw [((hyv.zpow_zpow i j)).mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
      mul_comm i, mul_comm j, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← hx9]
    exact N.mul_mem (N.zpow_mem (Subgroup.subset_closure (by simp)) _)
      (N.zpow_mem (Subgroup.subset_closure (by simp)) _)
  have hyS : y ∈ Subgroup.closure ({y, v} : Set G) := Subgroup.subset_closure (by simp)
  have hvS : v ∈ Subgroup.closure ({y, v} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm9 : x ^ 9 * v ^ 3 = v ^ 3 * x ^ 9 := by
    rw [hx9]
    exact ((hyv.pow_left 3).pow_right 3).eq
  refine ⟨v, ?_, ?_, ?_, 1, N.one_mem, by rw [mul_one, hv, hy']; group⟩
  ·
    intro hvN
    obtain ⟨i, j, hij⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hcomm9 hvN
    obtain ⟨n, hn⟩ := hP3 ⟨v, hvP⟩
    have hvn : v ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hvy : v ∈ Subgroup.zpowers y := by
      have e1 : v ^ (1 - 3 * j) = y ^ (3 * i) := by
        have e2 : v * (v ^ 3) ^ (-j) = (x ^ 9) ^ i := by
          nth_rewrite 1 [hij]
          rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
        have e3 : v ^ (1 - 3 * j) = v * (v ^ 3) ^ (-j) := by
          rw [← zpow_natCast v 3, ← zpow_mul, ← zpow_one_add]
          congr 1
          push_cast
          ring
        rw [e3, e2, hx9, ← zpow_natCast, ← zpow_mul]
        congr 1
      have hcop : IsCoprime (1 - 3 * j) ((3 : ℤ) ^ n) := by
        apply IsCoprime.pow_right
        exact ⟨1, j, by ring⟩
      obtain ⟨u, w, huw⟩ := hcop
      have hv3 : v ^ ((3 : ℤ) ^ n) = 1 := by exact_mod_cast hvn
      have : v = (v ^ (1 - 3 * j)) ^ u := by
        calc v = v ^ (u * (1 - 3 * j) + w * 3 ^ n) := by rw [huw, zpow_one]
          _ = (v ^ (1 - 3 * j)) ^ u := by
            rw [zpow_add, mul_comm w, zpow_mul v ((3 : ℤ) ^ n) w, hv3, one_zpow, mul_one,
              mul_comm u, zpow_mul]
      rw [this, e1]
      exact Subgroup.zpow_mem _ (Subgroup.zpow_mem_zpowers y _) _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hvy
    have hy'k : y' = y ^ (1 + k) := by rw [zpow_add, zpow_one, hk, hy'v]
    have hconj : ∀ m : ℤ, g⁻¹ * y ^ m * g = y ^ ((1 + k) * m) := by
      intro m
      rw [inv_mul_zpow_mul, ← hy', hy'k, ← zpow_mul]
    have hy''k : g⁻¹ * y' * g = y ^ ((1 + k) * (1 + k)) := by rw [hy'k, hconj]
    have hcub : y = y ^ ((1 + k) * ((1 + k) * (1 + k))) := by
      have e : g⁻¹ * (g⁻¹ * (g⁻¹ * y * g) * g) * g = y := by
        have : g⁻¹ * (g⁻¹ * (g⁻¹ * y * g) * g) * g = (g ^ 3)⁻¹ * y * g ^ 3 := by
          simp only [pow_succ, pow_zero, one_mul]
          group
        rw [this, hg3, inv_one, one_mul, mul_one]
      conv_lhs => rw [← e]
      rw [← hy', hy'k, hconj, hconj]
    have hk1 : (9 : ℤ) ∣ (1 + k) ^ 3 - 1 := by
      apply hy9
      rw [show (1 + k) ^ 3 - 1 = (1 + k) * ((1 + k) * (1 + k)) - 1 by ring, zpow_sub, zpow_one,
        ← hcub, mul_inv_cancel]
    have hk2 : (9 : ℤ) ∣ 1 + (1 + k) + (1 + k) ^ 2 := by
      apply hy9
      have e : y * y' * (g⁻¹ * y' * g) = y ^ (1 + (1 + k) + (1 + k) ^ 2) := by
        rw [hy''k, hy'k, ← zpow_one_add, ← zpow_add]
        congr 1
        ring
      rw [← e]
      exact h2
    exact not_dvd_of_cube_eq_one hk1 hk2
  ·
    have hy'S : y' ∈ Subgroup.closure ({y, v} : Set G) := by
      rw [hy'v]
      exact Subgroup.mul_mem _ hyS hvS
    have hgvS : g⁻¹ * v * g ∈ Subgroup.closure ({y, v} : Set G) := by
      have e : g⁻¹ * v * g = y'⁻¹ * (y * y')⁻¹ := by
        rw [← hy''inv, hv, hy']
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hy'S)
        (Subgroup.inv_mem _ (Subgroup.mul_mem _ hyS hy'S))
    have hg' : g⁻¹ ∈ Subgroup.normalizer (N : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      rw [inv_inv]
      have hle : N ≤ N.comap (MulAut.conj g⁻¹).toMonoidHom := by
        rw [hN, Subgroup.closure_le]
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        change g⁻¹ * w * g⁻¹⁻¹ ∈ N
        rw [inv_inv]
        rcases hw with rfl | rfl
        · rw [hx9, inv_mul_pow_mul, ← hy']
          exact hcube _ hy'S
        · rw [inv_mul_pow_mul]
          exact hcube _ hgvS
      have := hle hz
      rw [Subgroup.mem_comap] at this
      simpa using this
    simpa using inv_mem hg'
  ·
    intro z hz hzc
    have hyY : y ∈ Y := h.sec11K_le (Item1117Proof.x_cube_mem_sec11K h)
    have hgY : g ∈ Y := h.g_mem.1
    have hzd := h3 z hz (hzc y ⟨hyP, hyY⟩) (hzc g ⟨hgP, hgY⟩)
    have hd : d ∈ Subgroup.zpowers (y ^ 3) := by
      have h9 : 9 ∣ orderOf y := by
        have := hy9 (orderOf y) (by rw [zpow_natCast, pow_orderOf_eq_one])
        exact_mod_cast this
      exact Item1125Proof.mem_zpowers_pow_three (Item1117Proof.pow_three_of_mem_A h
        (Item1117Proof.d_mem_A h)) (Item1117Proof.d_mem_zpowers_x_cube h) h9
    rw [← hx9] at hd
    exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
      (Subgroup.zpowers_le.mpr hd hzd)

end Data

end Item1117Res3Proof

end CFSG.RankThree.PartTwo.Sec11

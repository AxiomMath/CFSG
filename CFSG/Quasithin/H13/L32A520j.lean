module

public import CFSG.Quasithin.H13.L32A520i

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Holt
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_two_three {A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 3 B) :
    A ⊓ B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact disjoint_iff.mp (IsPGroup.disjoint_of_ne 2 3 (by norm_num) A B hA hB)

theorem relIndex_sup_of_le_normalizer {D X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (X ⊔ D) = D.relIndex X := by
  have h1 := U3.relIndex_sup_eq (K := D) (T := X) hX
  have h2 := Subgroup.relIndex_mul_relIndex (D ⊓ X) X (X ⊔ D) inf_le_right le_sup_left
  have h3 := Subgroup.relIndex_mul_relIndex (D ⊓ X) D (X ⊔ D) inf_le_left le_sup_right
  rw [sup_comm] at h1
  rw [h1, ← h3, mul_comm] at h2
  have hpos : (D ⊓ X).relIndex D ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [← Subgroup.inf_relIndex_right D X]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) h2).symm

structure E9R (T L V H Y R : Subgroup G) : Prop extends E9Ctx T L V H Y where
  syl : fusionIsSylowIn 3 R (g1 T L V H Y)
  TN : T ≤ Subgroup.normalizer ((dT T L V H Y ⊔ R : Subgroup G) : Set G)
  YX : Y ≤ dT T L V H Y ⊔ R
  nc0 : ¬ R ≤ c0 H Y

abbrev pP (Y R : Subgroup G) : Subgroup G := R ⊓ Y

abbrev pP1 (T L V Y R : Subgroup G) : Subgroup G := R ⊓ (l1 T L V ⊔ pCoreOf 2 Y)

abbrev pP2 (T V Y R : Subgroup G) : Subgroup G := R ⊓ kY T V Y

omit [Finite G] in
theorem P_le_N_Q (Y R : Subgroup G) : pP Y R ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
  inf_le_right.trans (le_normalizer_pCoreOf 2 Y)

omit [Finite G] in
theorem P2_le_P (T V Y R : Subgroup G) : pP2 T V Y R ≤ pP Y R := fun _ hp =>
  ⟨hp.1, kY_le T V Y hp.2⟩

namespace E9R

variable {T L V H Y R : Subgroup G} (B : E9R T L V H Y R)
include B

theorem R_le_g1 : R ≤ g1 T L V H Y := B.syl.1

theorem R_le_c1 : R ≤ c1 T L V H Y := B.R_le_g1.trans inf_le_left

theorem R_le_H : R ≤ H := B.R_le_c1.trans (c1_le_H T L V H Y)

theorem R_le_N_D : R ≤ Subgroup.normalizer ((dT T L V H Y : Subgroup G) : Set G) :=
  B.R_le_g1.trans inf_le_right

theorem R3 : IsPGroup 3 R := B.syl.2.1

theorem D2 : IsPGroup 2 (dT T L V H Y) := B.S.hyp.fsu.sylow.1.to_le inf_le_left

theorem D_inf_R : dT T L V H Y ⊓ R = ⊥ := inf_eq_bot_of_two_three B.D2 B.R3

theorem Yp_le_N_D : dT T L V H Y ⊔ R ≤ Subgroup.normalizer ((dT T L V H Y : Subgroup G) : Set G) :=
  sup_le Subgroup.le_normalizer B.R_le_N_D

theorem Yp_le_H : dT T L V H Y ⊔ R ≤ H :=
  sup_le (inf_le_right.trans (c1_le_H T L V H Y)) B.R_le_H

theorem mem_Yp {g : G} (hg : g ∈ dT T L V H Y ⊔ R) : ∃ d ∈ dT T L V H Y, ∃ r ∈ R, g = d * r :=
  (F1.mem_sup_iff_exists_mul_of_normalizes B.R_le_N_D).mp hg

theorem eq_one_of_two {r : G} (hr : r ∈ R) {n : ℕ} (hn : r ^ 2 ^ n = 1) : r = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := B.R3 ⟨r, hr⟩
  have hm' : r ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn) (orderOf_dvd_of_pow_eq_one hm')
  rw [(Nat.Coprime.pow n m (by norm_num : Nat.Coprime 2 3)).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at hd
  exact hd

theorem pCore_eq : pCoreOf 2 (dT T L V H Y ⊔ R) = dT T L V H Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (fun x hx => ?_) (le_pCoreOf_of_le_normalizer 2 le_sup_left B.Yp_le_N_D B.D2)
  obtain ⟨d, hd, r, hr, rfl⟩ := B.mem_Yp (pCoreOf_le 2 _ hx)
  obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (dT T L V H Y ⊔ R) ⟨d * r, hx⟩
  have hn' : (d * r) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : r ^ 2 ^ n ∈ dT T L V H Y := by
    have := mul_pow_mem_of_mem (N := dT T L V H Y) (n := d) (g := r) hd (B.R_le_N_D hr) (2 ^ n)
    rw [hn', one_mul] at this
    simpa using (dT T L V H Y).inv_mem this
  have h3 : r ^ 2 ^ n = 1 := by
    have : r ^ 2 ^ n ∈ dT T L V H Y ⊓ R := ⟨h2, R.pow_mem hr _⟩
    rw [B.D_inf_R] at this
    exact this
  rw [B.eq_one_of_two hr h3, mul_one]
  exact hd

theorem Q_le_D : pCoreOf 2 Y ≤ dT T L V H Y := B.toE9Ctx.Q_le_D

theorem Y_inf_D : Y ⊓ dT T L V H Y = pCoreOf 2 Y := by
  refine le_antisymm (fun y hy => ?_) (le_inf (pCoreOf_le 2 Y) B.Q_le_D)
  obtain ⟨n, hn⟩ := B.D2 ⟨y, hy.2⟩
  exact B.toE9Ctx.mem_Q_of_two hy.1 (n := n) (by simpa using congrArg Subtype.val hn)

theorem mem_Y_of_mem_YD {r : G} (hr : r ∈ R) (hrY : r ∈ Y ⊔ dT T L V H Y) : r ∈ Y := by
  have hDY : dT T L V H Y ≤ Subgroup.normalizer (Y : Set G) :=
    (inf_le_right.trans (c1_le_H T L V H Y)).trans B.HY
  obtain ⟨y, hy, d, hd, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hDY).mp hrY
  obtain ⟨n, hn⟩ := B.D2 ⟨d, hd⟩
  have hn' : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h1 := mul_pow_mem_of_mem (N := Y) hy (hDY hd) (2 ^ n)
  rw [hn', inv_one, mul_one] at h1
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := B.R3 ⟨y * d, hr⟩
  have hm' : (y * d) ^ 3 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcop : Nat.Coprime (2 ^ n) (orderOf (y * d)) :=
    (Nat.Coprime.pow n m (by norm_num : Nat.Coprime 2 3)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hm')
  exact (Subgroup.zpowers_le.mpr h1) (A4.mem_zpowers_pow_of_coprime hcop)

theorem R_le_N_Y : R ≤ Subgroup.normalizer (Y : Set G) := B.R_le_H.trans B.HY

theorem R_le_N_P : R ≤ Subgroup.normalizer ((pP Y R : Subgroup G) : Set G) := fun _ hr =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hr, B.R_le_N_Y hr⟩

theorem Y_eq : pCoreOf 2 Y ⊔ pP Y R = Y := by
  refine le_antisymm (sup_le (pCoreOf_le 2 Y) inf_le_right) fun y hy => ?_
  obtain ⟨d, hd, r, hr, rfl⟩ := B.mem_Yp (B.YX hy)
  have hrY : r ∈ Y := by
    refine B.mem_Y_of_mem_YD hr ?_
    rw [show r = d⁻¹ * (d * r) by group, sup_comm]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (inv_mem hd)) (Subgroup.mem_sup_right hy)
  have hdY : d ∈ Y := by
    rw [show d = d * r * r⁻¹ by group]
    exact mul_mem hy (inv_mem hrY)
  have hdQ : d ∈ pCoreOf 2 Y := by
    rw [← B.Y_inf_D]
    exact ⟨hdY, hd⟩
  exact mul_mem (Subgroup.mem_sup_left hdQ) (Subgroup.mem_sup_right ⟨hr, hrY⟩)

theorem mem_Y {y : G} (hy : y ∈ Y) : ∃ q ∈ pCoreOf 2 Y, ∃ p ∈ pP Y R, y = q * p :=
  (F1.mem_sup_iff_exists_mul_of_normalizes (P_le_N_Q Y R)).mp (by rw [B.Y_eq]; exact hy)

theorem Q_inf_R : pCoreOf 2 Y ⊓ R = ⊥ :=
  inf_eq_bot_of_two_three (pCoreOf_isPGroup 2 Y) B.R3

theorem mem_R_inf_Q {x : G} (hxR : x ∈ R) (hxQ : x ∈ pCoreOf 2 Y) : x = 1 := by
  have : x ∈ pCoreOf 2 Y ⊓ R := ⟨hxQ, hxR⟩
  rw [B.Q_inf_R] at this
  exact this

theorem W_eq {W : Subgroup G} (hQW : pCoreOf 2 Y ≤ W) (hWY : W ≤ Y) :
    pCoreOf 2 Y ⊔ (R ⊓ W) = W := by
  refine le_antisymm (sup_le hQW inf_le_right) fun w hw => ?_
  obtain ⟨q, hq, p, hp, rfl⟩ := B.mem_Y (hWY hw)
  have hpW : p ∈ W := by
    rw [show p = q⁻¹ * (q * p) by group]
    exact mul_mem (hQW (inv_mem hq)) hw
  exact mul_mem (Subgroup.mem_sup_left hq) (Subgroup.mem_sup_right ⟨hp.1, hpW⟩)

theorem card_inf {W : Subgroup G} (hQW : pCoreOf 2 Y ≤ W) (hWY : W ≤ Y) :
    Nat.card ↥(R ⊓ W) = (pCoreOf 2 Y).relIndex W := by
  have hN : R ⊓ W ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    (inf_le_right.trans hWY).trans (le_normalizer_pCoreOf 2 Y)
  have h := relIndex_sup_of_le_normalizer hN
  rw [sup_comm, B.W_eq hQW hWY, ← Subgroup.inf_relIndex_right (pCoreOf 2 Y) (R ⊓ W)] at h
  have hb : pCoreOf 2 Y ⊓ (R ⊓ W) = ⊥ := by
    rw [← inf_assoc, B.Q_inf_R, bot_inf_eq]
  rw [hb, Subgroup.relIndex_bot_left] at h
  exact h.symm

theorem card_P : Nat.card ↥(pP Y R) = 9 := by
  rw [B.card_inf (pCoreOf_le 2 Y) le_rfl, B.toE9Ctx.card]

theorem card_P1 : Nat.card ↥(pP1 T L V Y R) = 3 := by
  rw [B.card_inf le_sup_right B.toE9Ctx.L1Q_le, B.toE9Ctx.L1Q3]

theorem card_P2 : Nat.card ↥(pP2 T V Y R) = 3 := by
  rw [B.card_inf B.toE9Ctx.Q_le_K (kY_le T V Y), B.toE9Ctx.K3]

theorem L1Q_eq : pCoreOf 2 Y ⊔ pP1 T L V Y R = l1 T L V ⊔ pCoreOf 2 Y :=
  B.W_eq le_sup_right B.toE9Ctx.L1Q_le

theorem K_eq : pCoreOf 2 Y ⊔ pP2 T V Y R = kY T V Y := B.W_eq B.toE9Ctx.Q_le_K (kY_le T V Y)

theorem P_comm {p p' : G} (hp : p ∈ pP Y R) (hp' : p' ∈ pP Y R) : p * p' = p' * p := by
  have h := B.toE9Ctx.comm p hp.2 p' hp'.2
  have hR : p * p' * p⁻¹ * p'⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hp.1 hp'.1) (R.inv_mem hp.1)) (R.inv_mem hp'.1)
  have h1 := B.mem_R_inf_Q hR h
  calc p * p' = p * p' * p⁻¹ * p'⁻¹ * (p' * p) := by group
    _ = p' * p := by rw [h1, one_mul]

theorem P_cube {p : G} (hp : p ∈ pP Y R) : p ^ 3 = 1 :=
  B.mem_R_inf_Q (R.pow_mem hp.1 3) (B.Y3 p hp.2)

theorem R_comm_P1 {r p : G} (hr : r ∈ R) (hp : p ∈ pP1 T L V Y R) : p * r = r * p := by
  have h := (mem_centralizerSection.mp (Subgroup.mem_inf.mp (B.R_le_c1 hr)).1).2.2.2 p hp.2
  have hR : p * r * p⁻¹ * r⁻¹ ∈ R :=
    R.mul_mem (R.mul_mem (R.mul_mem hp.1 hr) (R.inv_mem hp.1)) (R.inv_mem hr)
  have h1 := B.mem_R_inf_Q hR h
  calc p * r = p * r * p⁻¹ * r⁻¹ * (r * p) := by group
    _ = r * p := by rw [h1, one_mul]

theorem R_comm_P {r p : G} (hr : r ∈ R) (hp : p ∈ pP Y R) : p * r * p⁻¹ * r⁻¹ ∈ pP1 T L V Y R :=
  ⟨R.mul_mem (R.mul_mem (R.mul_mem hp.1 hr) (R.inv_mem hp.1)) (R.inv_mem hr),
    (mem_centralizerSection.mp (Subgroup.mem_inf.mp (B.R_le_c1 hr)).2).2.2.2 p hp.2⟩

theorem P1_le_P : pP1 T L V Y R ≤ pP Y R := fun _ hp => ⟨hp.1, B.toE9Ctx.L1Q_le hp.2⟩

theorem P1_inf_P2 : pP1 T L V Y R ⊓ pP2 T V Y R = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxQ : x ∈ pCoreOf 2 Y := by
    rw [← B.toE9Ctx.K_inf]
    exact ⟨hx.2.2, hx.1.2⟩
  exact B.mem_R_inf_Q hx.1.1 hxQ

theorem P_le : pP Y R ≤ pP2 T V Y R ⊔ pP1 T L V Y R := fun p hp => by
  have hpY := hp.2
  have hy' : p ∈ kY T V Y ⊔ (l1 T L V ⊔ pCoreOf 2 Y) := by rw [B.toE9Ctx.K_sup]; exact hpY
  obtain ⟨κ, hκ, ℓ, hℓ, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    (B.toE9Ctx.L1Q_le.trans B.toE9Ctx.Y_le_N_K)).mp hy'
  have hP2N : pP2 T V Y R ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    (P2_le_P T V Y R).trans (P_le_N_Q Y R)
  have hP1N : pP1 T L V Y R ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    B.P1_le_P.trans (P_le_N_Q Y R)
  obtain ⟨q₁, hq₁, p₂, hp₂, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hP2N).mp (by rw [B.K_eq]; exact hκ)
  obtain ⟨q₂, hq₂, p₁, hp₁, rfl⟩ :=
    (F1.mem_sup_iff_exists_mul_of_normalizes hP1N).mp (by rw [B.L1Q_eq]; exact hℓ)
  have hq' : q₁ * (p₂ * q₂ * p₂⁻¹) ∈ pCoreOf 2 Y :=
    mul_mem hq₁ ((Subgroup.mem_normalizer_iff.mp (hP2N hp₂) q₂).mp hq₂)
  have hq'R : q₁ * (p₂ * q₂ * p₂⁻¹) ∈ R := by
    rw [show q₁ * (p₂ * q₂ * p₂⁻¹) = q₁ * p₂ * (q₂ * p₁) * (p₂ * p₁)⁻¹ by group]
    exact R.mul_mem hp.1 (R.inv_mem (R.mul_mem hp₂.1 hp₁.1))
  have h1 := B.mem_R_inf_Q hq'R hq'
  rw [show q₁ * p₂ * (q₂ * p₁) = q₁ * (p₂ * q₂ * p₂⁻¹) * (p₂ * p₁) by group, h1, one_mul]
  exact mul_mem (Subgroup.mem_sup_left hp₂) (Subgroup.mem_sup_right hp₁)

end E9R

end CFSG.Quasithin.H13.L32A

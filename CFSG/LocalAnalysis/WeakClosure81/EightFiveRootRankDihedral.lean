module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveRootRankMod
import CFSG.Quasithin.H13.QRCFourFamilyBounds
import CFSG.CGT.Timmesfeld75.Sec3TwelveIrr
import CFSG.LocalAnalysis.WeakClosure81.SU3RankInvert
import CFSG.Timmesfeld.Orders.Bang
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic
open CFSG.Quasithin.H13.QRC

variable {F : Type} [AddCommGroup F] [Module (ZMod 2) F]

private theorem mul_pow_mul_eq_inv_pow {G : Type*} [Group G] {s z : G} (hs : s * s = 1)
    (hsz : s * z * s = z⁻¹) (k : ℕ) : s * z ^ k * s = (z ^ k)⁻¹ := by
  have hzs : z * s = s * z⁻¹ := by
    calc z * s = (s * s) * z * s := by rw [hs, one_mul]
      _ = s * (s * z * s) := by group
      _ = s * z⁻¹ := by rw [hsz]
  induction k with
  | zero => simpa using hs
  | succ n ih =>
    calc s * z ^ (n + 1) * s
        = (s * z ^ n) * (z * s) := by rw [pow_succ]; group
      _ = (s * z ^ n) * (s * z⁻¹) := by rw [hzs]
      _ = (s * z ^ n * s) * z⁻¹ := by group
      _ = (z ^ n)⁻¹ * z⁻¹ := by rw [ih]
      _ = (z ^ (n + 1))⁻¹ := by rw [← inv_pow, ← inv_pow, pow_succ]

private theorem orderOf_dvd_natCard_sub_one_of_free [Finite F] {y z : LGL 2 F}
    {W : Submodule (ZMod 2) F} (hW : W = LinearMap.range ((z : F →ₗ[ZMod 2] F) - LinearMap.id))
    (hyz : y * z = z * y)
    (hfree : ∀ i : ℕ, 0 < i → i < orderOf y → ∀ w : F, w ∈ W → (y ^ i) w = w → w = 0) :
    orderOf y ∣ Nat.card W - 1 := by
  classical
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have : Finite (LGL 2 F) :=
    Finite.of_injective (fun f : LGL 2 F => (f : F → F))
      (fun f g h => LinearEquiv.ext (congrFun h))
  have : Finite W := Subtype.finite
  have hcomm : ∀ g ∈ Subgroup.zpowers y, g * z = z * g := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact ((show Commute y z from hyz).zpow_left k).eq
  let act : ↥(Subgroup.zpowers y) → W → W := fun p v =>
    ⟨(p : LGL 2 F) (v : F),
      Eq.mpr (congrArg (fun S : Submodule (ZMod 2) F => (p : LGL 2 F) (v : F) ∈ S) hW)
        (mem_range_sub_of_commute (hcomm p p.2)
          (Eq.mp (congrArg (fun S : Submodule (ZMod 2) F => (v : F) ∈ S) hW) v.2))⟩
  let _ : SMul ↥(Subgroup.zpowers y) W := ⟨act⟩
  let _ : MulAction ↥(Subgroup.zpowers y) W :=
    { one_smul := fun v => Subtype.ext (by
        change (act 1 v : F) = (v : F)
        simp [act])
      mul_smul := fun p q v => Subtype.ext (by
        change (act (p * q) v : F) = (act p (act q v) : F)
        simp [act, Subgroup.coe_mul, LinearEquiv.mul_apply]) }
  have hdvd := CFSG.CGT.Timmesfeld75.irr_card_dvd_sub_one (P := ↥(Subgroup.zpowers y))
    (X := W) (0 : W) (fun p => Subtype.ext (by
      change (act p 0 : F) = (0 : F)
      simp [act])) (by
      intro p x hp hx
      have hx' : (p : LGL 2 F) (x : F) = (x : F) := by
        have h := congrArg Subtype.val hx
        change (p : LGL 2 F) (x : F) = (x : F) at h
        exact h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp p.2
      by_cases hk0 : k % (orderOf y : ℤ) = 0
      · have hp1 : (p : LGL 2 F) = 1 := by
          rw [← hk, zpow_eq_zpow_emod' k (pow_orderOf_eq_one y), hk0, zpow_zero]
        exact absurd (Subtype.ext hp1) hp
      · let i : ℕ := (k % (orderOf y : ℤ)).toNat
        have hnonneg : 0 ≤ k % (orderOf y : ℤ) :=
          Int.emod_nonneg k (by exact_mod_cast (orderOf_pos y).ne')
        have hcast : (i : ℤ) = k % (orderOf y : ℤ) := Int.toNat_of_nonneg hnonneg
        have hi_lt : i < orderOf y := by
          have hlt : k % (orderOf y : ℤ) < (orderOf y : ℤ) :=
            Int.emod_lt_of_pos k (by exact_mod_cast orderOf_pos y)
          omega
        have hne : (i : ℤ) ≠ 0 := by rw [hcast]; exact hk0
        have hi_pos : 0 < i := by omega
        have hik : y ^ k = y ^ i := by
          rw [zpow_eq_zpow_emod' k (pow_orderOf_eq_one y), ← hcast, zpow_natCast]
        have hfix : (y ^ i) (x : F) = (x : F) := by
          rw [← hik, hk]
          exact hx'
        exact Subtype.ext (hfree i hi_pos hi_lt (x : F) x.2 hfix))
  rwa [Nat.card_zpowers] at hdvd

private theorem eq_zero_of_pow_apply_eq_self_of_pow_nine {y : LGL 2 F} (hy : y ^ 9 = 1)
    (hy3 : y ^ 3 ≠ 1) {i : ℕ} (hi0 : 0 < i) (hi9 : i < 9) {w : F}
    (hw : w ∈ LinearMap.range (((y ^ 3 : LGL 2 F) : F →ₗ[ZMod 2] F) - LinearMap.id))
    (hfix : (y ^ i) w = w) : w = 0 := by
  have hz3 : (y ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 by norm_num, hy]
  have hzord : orderOf (y ^ 3) = 3 := orderOf_eq_prime hz3 hy3
  have hzodd : Odd (orderOf (y ^ 3)) := by rw [hzord]; decide
  by_cases h3 : 3 ∣ i
  · obtain ⟨k, rfl⟩ := h3
    have hk : k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl
    · have hfix' : (y ^ 3) w = w := by simpa using hfix
      exact eq_zero_of_mem_range_sub_of_fixed hzodd hw hfix'
    · have hfix6 : (y ^ 6) w = w := by simpa using hfix
      have hfixz : (y ^ 3) w = w := by
        calc (y ^ 3) w = (y ^ 3) ((y ^ 6) w) := by rw [hfix6]
          _ = ((y ^ 3) * (y ^ 6)) w := (LinearEquiv.mul_apply (y ^ 3) (y ^ 6) w).symm
          _ = (y ^ 9) w := by rw [← pow_add]
          _ = w := by rw [hy]; rfl
      exact eq_zero_of_mem_range_sub_of_fixed hzodd hw hfixz
  · have hcop : Nat.Coprime i 9 := by
      have h := Nat.prime_three.coprime_pow_of_not_dvd (m := 2) h3
      simpa using h
    have hord9 : orderOf y = 9 := orderOf_eq_prime_pow (p := 3) (n := 1)
      (by simpa using hy3) (by simpa using hy)
    have hmem : y ∈ Subgroup.zpowers (y ^ i) := by
      rw [mem_zpowers_pow_iff, hord9]
      exact hcop
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hyw : y w = w := by
      rw [← hm]
      exact zpow_apply_eq_self hfix m
    have hzw : (y ^ 3) w = w := pow_apply_eq_self hyw 3
    exact eq_zero_of_mem_range_sub_of_fixed hzodd hw hzw

private theorem six_le_finrank_range_pow_three_sub [Finite F] {y : LGL 2 F} (hy : y ^ 9 = 1)
    (hy3 : y ^ 3 ≠ 1) : 6 ≤ Module.finrank (ZMod 2)
      (LinearMap.range (((y ^ 3 : LGL 2 F) : F →ₗ[ZMod 2] F) - LinearMap.id)) := by
  classical
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  let z : LGL 2 F := y ^ 3
  let W : Submodule (ZMod 2) F := LinearMap.range ((z : F →ₗ[ZMod 2] F) - LinearMap.id)
  have : Finite W := Subtype.finite
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hz3 : z ^ 3 = 1 := by
    dsimp only [z]
    rw [← pow_mul, show 3 * 3 = 9 by norm_num, hy]
  have hWne : W ≠ ⊥ := by
    intro hbot
    apply hy3
    have hz1 : z = 1 := by
      apply LinearEquiv.ext
      intro v
      have hzv : (z : F →ₗ[ZMod 2] F) v = v := by
        have h := congrArg (fun f : F →ₗ[ZMod 2] F => f v)
          (LinearMap.range_eq_bot.mp (show LinearMap.range
            ((z : F →ₗ[ZMod 2] F) - LinearMap.id) = ⊥ from hbot))
        simpa using sub_eq_zero.mp h
      simpa using hzv
    exact hz1
  have hord9 : orderOf y = 9 := orderOf_eq_prime_pow (p := 3) (n := 1)
    (by simpa using hy3) (by simpa using hy)
  have hyz : y * z = z * y := ((Commute.refl y).pow_right 3).eq
  have hfree : ∀ i : ℕ, 0 < i → i < orderOf y → ∀ w : F, w ∈ W → (y ^ i) w = w → w = 0 := by
    intro i hi0 hiord w hw hfix
    rw [hord9] at hiord
    exact eq_zero_of_pow_apply_eq_self_of_pow_nine hy hy3 hi0 hiord hw hfix
  have hdvd : orderOf y ∣ Nat.card W - 1 :=
    orderOf_dvd_natCard_sub_one_of_free (y := y) (z := z) (W := W) rfl hyz hfree
  rw [hord9] at hdvd
  have hcardW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardW] at hdvd
  have h6dvd : 6 ∣ Module.finrank (ZMod 2) W := by
    have h := orderOf_dvd_of_pow_eq_one ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mp hdvd)
    have horder : orderOf (2 : ZMod 9) = 6 := by
      rw [orderOf_eq_iff (by norm_num)]
      refine ⟨by decide, ?_⟩
      intro m hm h0
      interval_cases m <;> decide
    rwa [horder] at h
  have hdpos : 0 < Module.finrank (ZMod 2) W := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hWne ((Submodule.finrank_eq_zero (R := ZMod 2)).1 h0)
  have h6 : 6 ≤ Module.finrank (ZMod 2) W := Nat.le_of_dvd hdpos h6dvd
  simpa [W, z] using h6

theorem orderOf_two_le_two_mul_modCommRank {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    [Finite F] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {s y : LGL 2 F} (hs : s * s = 1)
    (hsy : s * y * s = y⁻¹) (hy : y ^ p = 1) (hy1 : y ≠ 1) :
    orderOf (2 : ZMod p) ≤ 2 * modCommRank s := by
  classical
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hoddp : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hordy : orderOf y = p := orderOf_eq_prime hy hy1
  have hzodd : Odd (orderOf y) := by rw [hordy]; exact hoddp
  have hcore := finrank_range_sub_le_two_mul_modCommRank hs hsy hzodd
  let W : Submodule (ZMod 2) F := LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id)
  have : Finite W := Subtype.finite
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have hfree : ∀ i : ℕ, 0 < i → i < orderOf y → ∀ w : F, w ∈ W → (y ^ i) w = w → w = 0 := by
    intro i hi0 hiord w hw hfix
    rw [hordy] at hiord
    have hpndvd : ¬ p ∣ i := Nat.not_dvd_of_pos_of_lt hi0 hiord
    have hyw : y w = w := apply_eq_self_of_pow (Fact.out : p.Prime) hy hpndvd hfix
    exact eq_zero_of_mem_range_sub_of_fixed hzodd hw hyw
  have hdvd : orderOf y ∣ Nat.card W - 1 :=
    orderOf_dvd_natCard_sub_one_of_free (y := y) (z := y) (W := W) rfl (by rfl) hfree
  rw [hordy] at hdvd
  have hcardW : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  rw [hcardW] at hdvd
  have hdvd' : orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) W :=
    orderOf_dvd_of_pow_eq_one ((CFSG.Timmesfeld.Bang.dvd_two_pow_sub_one_iff _).mp hdvd)
  have hdpos : 0 < Module.finrank (ZMod 2) W := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have hbot : LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id) = ⊥ := by
      change W = ⊥
      exact (Submodule.finrank_eq_zero (R := ZMod 2)).1 h0
    have hy1' : y = 1 := by
      apply LinearEquiv.ext
      intro v
      have hyv : (y : F →ₗ[ZMod 2] F) v = v := by
        have h := congrArg (fun f : F →ₗ[ZMod 2] F => f v) (LinearMap.range_eq_bot.mp hbot)
        simpa using sub_eq_zero.mp h
      simpa using hyv
    exact hy1 hy1'
  have hle : orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) W :=
    Nat.le_of_dvd hdpos hdvd'
  exact le_trans hle hcore

theorem three_le_modCommRank_of_pow_nine {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    [Finite F] {s y : LGL 2 F} (hs : s * s = 1) (hsy : s * y * s = y⁻¹) (hy : y ^ 9 = 1)
    (hy3 : y ^ 3 ≠ 1) : 3 ≤ modCommRank s := by
  classical
  have : Module.Finite (ZMod 2) F := Module.Finite.of_finite
  have hz3 : (y ^ 3) ^ 3 = 1 := by
    rw [← pow_mul, show 3 * 3 = 9 by norm_num, hy]
  have hsz : s * (y ^ 3) * s = (y ^ 3)⁻¹ := mul_pow_mul_eq_inv_pow hs hsy 3
  have hcore := finrank_range_sub_le_two_mul_modCommRank hs hsz
    (Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hz3))
  have h6 := six_le_finrank_range_pow_three_sub hy hy3
  omega

end CFSG.LocalAnalysis.WeakClosure81

end

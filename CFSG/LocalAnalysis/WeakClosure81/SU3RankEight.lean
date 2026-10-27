module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
import CFSG.LocalAnalysis.WeakClosure81.SU3RankPrimePower
import CFSG.LocalAnalysis.WeakClosure81.TenFive
import CFSG.SignalizerFunctorTheorem.Quadratic.Offenders

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

variable {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Finite F]

private theorem orderOf_two_zmod_nine : orderOf (2 : ZMod (3 ^ 2)) = 6 := by
  rw [orderOf_eq_iff (by norm_num : 0 < 6)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

private theorem mem_fixSub_zpowers_of_apply_eq {g : LGL 2 F} {w : F} (h : g w = w) :
    w ∈ fixSub (Subgroup.zpowers g) := by
  intro a ha
  have hstab : g ∈ MulAction.stabilizer (LGL 2 F) w := by
    rw [MulAction.mem_stabilizer_iff]
    simpa [LinearEquiv.smul_def] using h
  have hle : Subgroup.zpowers g ≤ MulAction.stabilizer (LGL 2 F) w :=
    Subgroup.zpowers_le.mpr hstab
  have := hle ha
  rwa [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at this

private theorem map_mem_range_sub_id_of_conj {g y z : LGL 2 F}
    (hconj : ∀ v : F, g (y v) = z (g v))
    (hz : ∀ u : F, z u - u ∈ LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id))
    {w : F} (hw : w ∈ LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id)) :
    g w ∈ LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id) := by
  obtain ⟨v, rfl⟩ := hw
  have h1 : g (((y : F →ₗ[ZMod 2] F) - (LinearMap.id : F →ₗ[ZMod 2] F)) v) =
      z (g v) - g v := by
    rw [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      show g ((y : F →ₗ[ZMod 2] F) v) = z (g v) from hconj v]
  rw [h1]
  exact hz (g v)

private theorem avg_decomposition (x y : LGL 2 F) (hxy : x * y = y * x) (hy3 : y ^ 3 = 1) :
    (1 : Module.End (ZMod 2) F) =
      (1 + (y : Module.End (ZMod 2) F) + (y : Module.End (ZMod 2) F) ^ 2) +
      (1 + (x : Module.End (ZMod 2) F) + (x : Module.End (ZMod 2) F) ^ 2) +
      (1 + ((x * y : LGL 2 F) : Module.End (ZMod 2) F) +
            ((x * y : LGL 2 F) : Module.End (ZMod 2) F) ^ 2) +
      (1 + ((x * y ^ 2 : LGL 2 F) : Module.End (ZMod 2) F) +
            ((x * y ^ 2 : LGL 2 F) : Module.End (ZMod 2) F) ^ 2) +
      (1 + (x : Module.End (ZMod 2) F) + (x : Module.End (ZMod 2) F) ^ 2) *
        (1 + (y : Module.End (ZMod 2) F) + (y : Module.End (ZMod 2) F) ^ 2) := by
  let X : Module.End (ZMod 2) F := x
  let Y : Module.End (ZMod 2) F := y
  change (1 : Module.End (ZMod 2) F) =
    (1 + Y + Y ^ 2) + (1 + X + X ^ 2) + (1 + X * Y + (X * Y) ^ 2) +
      (1 + X * Y ^ 2 + (X * Y ^ 2) ^ 2) + (1 + X + X ^ 2) * (1 + Y + Y ^ 2)
  have hXY : Commute X Y := by
    change (x : Module.End (ZMod 2) F) * (y : Module.End (ZMod 2) F) =
      (y : Module.End (ZMod 2) F) * (x : Module.End (ZMod 2) F)
    simpa using congrArg (fun f : LGL 2 F => (f : Module.End (ZMod 2) F)) hxy
  have hY3 : Y ^ 3 = (1 : Module.End (ZMod 2) F) := by
    change ((y ^ 3 : LGL 2 F) : Module.End (ZMod 2) F) = 1
    rw [hy3]
    rfl
  have hXY2 : (X * Y) ^ 2 = X ^ 2 * Y ^ 2 := hXY.mul_pow 2
  have hcomm2 : Commute X (Y ^ 2) := hXY.pow_right 2
  have hXY22 : (X * Y ^ 2) ^ 2 = X ^ 2 * Y := by
    rw [hcomm2.mul_pow 2]
    congr 1
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, pow_succ, hY3, one_mul]
  have h2 : ∀ z : Module.End (ZMod 2) F, (2 : ℤ) • z = 0 := by
    intro z
    rw [← Int.cast_smul_eq_zsmul (ZMod 2)]
    rw [show (((2 : ℤ)) : ZMod 2) = 0 by decide, zero_smul]
  have h5 : (5 : ℤ) • (1 : Module.End (ZMod 2) F) = 1 := by
    rw [← Int.cast_smul_eq_zsmul (ZMod 2)]
    rw [show (((5 : ℤ)) : ZMod 2) = 1 by decide, one_smul]
  rw [hXY2, hXY22]
  noncomm_ring
  simp only [h2, h5, add_zero]

private theorem avg_pointwise (x y : LGL 2 F) (hxy : x * y = y * x) (hy3 : y ^ 3 = 1)
    (w : F) :
    w = (w + y w + (y ^ 2) w) + (w + x w + (x ^ 2) w) +
      (w + (x * y) w + ((x * y) ^ 2) w) + (w + (x * y ^ 2) w + ((x * y ^ 2) ^ 2) w) +
      (((1 + (x : Module.End (ZMod 2) F) + (x : Module.End (ZMod 2) F) ^ 2) *
        (1 + (y : Module.End (ZMod 2) F) + (y : Module.End (ZMod 2) F) ^ 2) :
          Module.End (ZMod 2) F) w) := by
  have h := congrArg (fun f : Module.End (ZMod 2) F => f w) (avg_decomposition x y hxy hy3)
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearEquiv.mul_apply] at h
  exact h

private theorem add_add_sq_eq_zero_of_fix_free {b : LGL 2 F} {M : Submodule (ZMod 2) F}
    (hb3 : b ^ 3 = 1) (hbM : ∀ w ∈ M, b w ∈ M)
    (hfix : ∀ w ∈ M, b w = w → w = 0) {w : F} (hw : w ∈ M) :
    w + b w + (b ^ 2) w = 0 := by
  have hsq : (b ^ 2) w = b (b w) := by rw [pow_two, LinearEquiv.mul_apply]
  have hmem : w + b w + (b ^ 2) w ∈ M := by
    rw [hsq]
    exact M.add_mem (M.add_mem hw (hbM w hw)) (hbM (b w) (hbM w hw))
  have hfixp : b (w + b w + (b ^ 2) w) = w + b w + (b ^ 2) w := by
    rw [map_add, map_add,
      show b (b w) = (b ^ 2) w by rw [← LinearEquiv.mul_apply, pow_two],
      show b ((b ^ 2) w) = w by
        rw [← LinearEquiv.mul_apply, ← pow_succ', show 2 + 1 = 3 by norm_num, hb3]
        rfl]
    abel
  exact hfix _ hmem hfixp

private theorem six_dvd_finrank_of_invariant {y s : LGL 2 F} (hs : s ^ 3 = y) (hy3 : y ^ 3 = 1)
    (hfixfree : ∀ w ∈ commSub (Subgroup.zpowers y), y w = w → w = 0)
    {M : Submodule (ZMod 2) F} (hMW : M ≤ commSub (Subgroup.zpowers y))
    (hsM : ∀ x ∈ M, s x ∈ M) : 6 ∣ Module.finrank (ZMod 2) M := by
  have hs9 : s ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hs, hy3]
  have hfixM : ∀ x ∈ M, (s ^ (3 ^ (2 - 1))) x = x → x = 0 := by
    intro x hxM hx
    refine hfixfree x (hMW hxM) ?_
    rw [show 3 ^ (2 - 1) = 3 by norm_num] at hx
    rwa [hs] at hx
  have h := orderOf_two_dvd_finrank_of_pow_prime_pow (W := F) (ℓ := 3) (k := 2)
    Nat.prime_three (by norm_num) (by norm_num) hs9 M hsM hfixM
  rwa [orderOf_two_zmod_nine] at h

private theorem fixed_eq_bot_or_top {y s b : LGL 2 F} (hs : s ^ 3 = y) (hy3 : y ^ 3 = 1)
    (hbs : b * s = s * b)
    (hsW : ∀ w ∈ commSub (Subgroup.zpowers y), s w ∈ commSub (Subgroup.zpowers y))
    (hfixfree : ∀ w ∈ commSub (Subgroup.zpowers y), y w = w → w = 0)
    (hdim : Module.finrank (ZMod 2) (commSub (Subgroup.zpowers y)) = 6) :
    commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b) = ⊥ ∨
      commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b) =
        commSub (Subgroup.zpowers y) := by
  have hsC : ∀ w ∈ commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b),
      s w ∈ commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b) := by
    intro w hw
    have hbw : b w = w :=
      (mem_fixSub (A := Subgroup.zpowers b)).mp hw.2 b (Subgroup.mem_zpowers b)
    refine ⟨hsW w hw.1, ?_⟩
    apply mem_fixSub_zpowers_of_apply_eq
    rw [← LinearEquiv.mul_apply, hbs, LinearEquiv.mul_apply, hbw]
  have hdvd := six_dvd_finrank_of_invariant hs hy3 hfixfree inf_le_left hsC
  by_cases hbot : commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b) = ⊥
  · exact Or.inl hbot
  · refine Or.inr ?_
    have hpos : 0 < Module.finrank (ZMod 2)
        ↥(commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b)) := by
      by_contra h0
      exact hbot ((Submodule.finrank_eq_zero).mp (Nat.eq_zero_of_not_pos h0))
    have h6 := Nat.le_of_dvd hpos hdvd
    have hle := Submodule.finrank_mono
      (inf_le_left : commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b) ≤
        commSub (Subgroup.zpowers y))
    have heq : Module.finrank (ZMod 2)
          ↥(commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b)) =
        Module.finrank (ZMod 2) (commSub (Subgroup.zpowers y)) := by omega
    exact Submodule.eq_of_le_of_finrank_eq inf_le_left heq

private theorem fixfree_of_fixed_eq_bot {y b : LGL 2 F}
    (h : commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b) = ⊥) :
    ∀ w ∈ commSub (Subgroup.zpowers y), b w = w → w = 0 := by
  intro w hw hbw
  have hwfix : w ∈ fixSub (Subgroup.zpowers b) := mem_fixSub_zpowers_of_apply_eq hbw
  have : w ∈ commSub (Subgroup.zpowers y) ⊓ fixSub (Subgroup.zpowers b) := ⟨hw, hwfix⟩
  rw [h] at this
  simpa using this

private theorem mul_pointwise {A B : LGL 2 F} {M : Submodule (ZMod 2) F}
    (hA : ∀ w ∈ M, A w = w) (hB : ∀ w ∈ M, B w = w) :
    ∀ w ∈ M, (A * B) w = w := by
  intro w hw
  rw [LinearEquiv.mul_apply, hB w hw, hA w hw]

private theorem inv_pointwise {A : LGL 2 F} {M : Submodule (ZMod 2) F}
    (hA : ∀ w ∈ M, A w = w) : ∀ w ∈ M, A⁻¹ w = w := by
  intro w hw
  have h := congrArg A.symm (hA w hw)
  rw [A.symm_apply_apply] at h
  exact h.symm

private theorem inv_mem_of_map_mem {g : LGL 2 F} {M : Submodule (ZMod 2) F}
    (hgM : ∀ w ∈ M, g w ∈ M) {w : F} (hw : w ∈ M) : g⁻¹ w ∈ M := by
  let f : M → M := fun x => ⟨g x, hgM x x.2⟩
  have hf : Function.Injective f := fun x y hxy => by
    apply Subtype.ext
    exact g.injective (Subtype.ext_iff.mp hxy)
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hf ⟨w, hw⟩
  have hgu : g (u : F) = w := congrArg Subtype.val hu
  rw [← hgu]
  change g.symm (g (u : F)) ∈ M
  rw [g.symm_apply_apply]
  exact u.2

theorem twelve_le_finrank_range_sub_of_cube {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    [Finite F] {y s x t c : LGL 2 F} (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) (hs : s ^ 3 = y)
    (hx3 : x ^ 3 = 1) (hxs : x * s = s * x) (hty : t * y * t⁻¹ = y⁻¹) (htx : t * x * t⁻¹ = x)
    (hcy : c * y * c⁻¹ = y) (hcx : c * x * c⁻¹ = x * y ∨ c * x * c⁻¹ = x * y⁻¹) :
    12 ≤ Module.finrank (ZMod 2) (LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id)) := by
  have horder : orderOf y = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hy3) with h | h
    · exact absurd h (fun h1 => hy1 (orderOf_eq_one_iff.mp h1))
    · exact h
  let W : Submodule (ZMod 2) F := commSub (Subgroup.zpowers y)
  have hWrange : W = LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id) :=
    commSub_zpowers y
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, horder]
    norm_num
  have hWne : W ≠ ⊥ := by
    intro h
    exact hy1 (Subgroup.zpowers_eq_bot.mp ((commSub_eq_bot_iff (Subgroup.zpowers y)).mp h))
  have hcompl : IsCompl (fixSub (Subgroup.zpowers y)) W :=
    isCompl_fixSub_commSub_of_odd (Subgroup.zpowers y) hodd
  have hfixfree : ∀ w ∈ W, y w = w → w = 0 := by
    intro w hw hyw
    have hwfix : w ∈ fixSub (Subgroup.zpowers y) := mem_fixSub_zpowers_of_apply_eq hyw
    have hbot : fixSub (Subgroup.zpowers y) ⊓ W = ⊥ := hcompl.inf_eq_bot
    have hmem : w ∈ fixSub (Subgroup.zpowers y) ⊓ W := ⟨hwfix, hw⟩
    rw [hbot] at hmem
    simpa using hmem
  have hyW : ∀ w ∈ W, y w ∈ W := fun w hw => map_mem_commSub _ (Subgroup.mem_zpowers y) hw
  have hxy : Commute x y := by
    have h : Commute x (s ^ 3) := (show Commute x s from hxs).pow_right 3
    rwa [hs] at h
  have hsy : Commute s y := by
    have h : Commute s (s ^ 3) := (Commute.refl s).pow_right 3
    rwa [hs] at h
  have hys : Commute y s := hsy.symm
  have hcy : Commute c y := by
    have h : c * y = y * c := by
      have := congrArg (fun z => z * c) hcy
      simpa using this
    exact h
  have hciy : Commute c⁻¹ y := hcy.inv_left
  have hty_comm : t * y = y⁻¹ * t := by
    have := congrArg (fun z => z * t) hty
    simpa using this
  have hy_inv_eq : y⁻¹ = y ^ 2 := by
    rw [inv_eq_iff_mul_eq_one]
    rw [← pow_succ', show 2 + 1 = 3 by norm_num, hy3]
  have hty2 : t * y * t⁻¹ = y ^ 2 := by rw [hty, hy_inv_eq]
  have hzy : ∀ u : F, y u - u ∈ LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id) := by
    intro u
    rw [← commSub_zpowers y]
    exact sub_mem_commSub _ (Subgroup.mem_zpowers y) u
  have hzyinv : ∀ u : F,
      y⁻¹ u - u ∈ LinearMap.range ((y : F →ₗ[ZMod 2] F) - LinearMap.id) := by
    intro u
    rw [← commSub_zpowers y]
    exact sub_mem_commSub _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y)) u
  have hxW : ∀ w ∈ W, x w ∈ W := by
    intro w hw
    rw [hWrange] at hw ⊢
    refine map_mem_range_sub_id_of_conj (g := x) (y := y) (z := y) ?_ (fun u => hzy u) hw
    intro v
    have := congrArg (fun f : LGL 2 F => f v) hxy
    simpa [LinearEquiv.mul_apply] using this
  have hsW : ∀ w ∈ W, s w ∈ W := by
    intro w hw
    rw [hWrange] at hw ⊢
    refine map_mem_range_sub_id_of_conj (g := s) (y := y) (z := y) ?_ (fun u => hzy u) hw
    intro v
    have := congrArg (fun f : LGL 2 F => f v) hsy
    simpa [LinearEquiv.mul_apply] using this
  have hcW : ∀ w ∈ W, c w ∈ W := by
    intro w hw
    rw [hWrange] at hw ⊢
    refine map_mem_range_sub_id_of_conj (g := c) (y := y) (z := y) ?_ (fun u => hzy u) hw
    intro v
    have := congrArg (fun f : LGL 2 F => f v) hcy
    simpa [LinearEquiv.mul_apply] using this
  have htW : ∀ w ∈ W, t w ∈ W := by
    intro w hw
    rw [hWrange] at hw ⊢
    refine map_mem_range_sub_id_of_conj (g := t) (y := y) (z := y⁻¹) ?_
      (fun u => hzyinv u) hw
    intro v
    have := congrArg (fun f : LGL 2 F => f v) hty_comm
    simpa [LinearEquiv.mul_apply] using this
  have htiW : ∀ w ∈ W, t⁻¹ w ∈ W := fun w hw => inv_mem_of_map_mem htW hw
  have hciW : ∀ w ∈ W, c⁻¹ w ∈ W := fun w hw => inv_mem_of_map_mem hcW hw
  have hmulW : ∀ {A B : LGL 2 F}, (∀ w ∈ W, A w ∈ W) → (∀ w ∈ W, B w ∈ W) →
      ∀ w ∈ W, (A * B) w ∈ W := by
    intro A B hA hB w hw
    rw [LinearEquiv.mul_apply]
    exact hA _ (hB w hw)
  have hy2W : ∀ w ∈ W, (y ^ 2) w ∈ W := by
    intro w hw
    rw [pow_two, LinearEquiv.mul_apply]
    exact hyW _ (hyW w hw)
  have hxyW : ∀ w ∈ W, (x * y) w ∈ W := hmulW hxW hyW
  have hxy2W : ∀ w ∈ W, (x * y ^ 2) w ∈ W := hmulW hxW hy2W
  have hxys : (x * y) * s = s * (x * y) := by
    rw [mul_assoc, show y * s = s * y from hys, ← mul_assoc, hxs, mul_assoc]
  have hy2s : y ^ 2 * s = s * y ^ 2 := hys.pow_left 2
  have hxy2s : (x * y ^ 2) * s = s * (x * y ^ 2) := by
    rw [mul_assoc, hy2s, ← mul_assoc, hxs, mul_assoc]
  have pointwise_of_eq : ∀ {b : LGL 2 F},
      W ⊓ fixSub (Subgroup.zpowers b) = W → ∀ w ∈ W, b w = w := by
    intro b hb w hw
    have hmem : w ∈ W ⊓ fixSub (Subgroup.zpowers b) := by rw [hb]; exact hw
    exact (mem_fixSub (A := Subgroup.zpowers b)).mp hmem.2 b (Subgroup.mem_zpowers b)
  have pointwise_t : ∀ {A : LGL 2 F} (_ : ∀ w ∈ W, A w = w),
      ∀ w ∈ W, (t * A * t⁻¹) w = w := by
    intro A hA w hw
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hA _ (htiW w hw)]
    exact t.apply_symm_apply w
  have hallbot : W ⊓ fixSub (Subgroup.zpowers x) = ⊥ →
      W ⊓ fixSub (Subgroup.zpowers (x * y)) = ⊥ →
      W ⊓ fixSub (Subgroup.zpowers (x * y ^ 2)) = ⊥ → False := by
    intro h1 h2 h3
    have hfixx := fixfree_of_fixed_eq_bot (y := y) (b := x) h1
    have hfixxy := fixfree_of_fixed_eq_bot (y := y) (b := x * y) h2
    have hfixxy2 := fixfree_of_fixed_eq_bot (y := y) (b := x * y ^ 2) h3
    have hxy3 : (x * y) ^ 3 = 1 := by
      rw [hxy.mul_pow 3, hx3, hy3, mul_one]
    have hy23 : (y ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, show 2 * 3 = 6 by norm_num, show (6 : ℕ) = 3 + 3 by norm_num,
        pow_add, hy3, one_mul]
    have hxy23 : (x * y ^ 2) ^ 3 = 1 := by
      rw [(hxy.pow_right 2).mul_pow 3, hx3, hy23, mul_one]
    apply hWne
    have hle : W ≤ ⊥ := fun w hw => by
      have hy0 := add_add_sq_eq_zero_of_fix_free hy3 hyW hfixfree hw
      have hx0 := add_add_sq_eq_zero_of_fix_free hx3 hxW hfixx hw
      have hxy0 := add_add_sq_eq_zero_of_fix_free hxy3 hxyW hfixxy hw
      have hxy20 := add_add_sq_eq_zero_of_fix_free hxy23 hxy2W hfixxy2 hw
      have h := avg_pointwise x y hxy hy3 w
      rw [hy0, hx0, hxy0, hxy20] at h
      have h5th : (((1 + (x : Module.End (ZMod 2) F) + (x : Module.End (ZMod 2) F) ^ 2) *
          (1 + (y : Module.End (ZMod 2) F) + (y : Module.End (ZMod 2) F) ^ 2) :
            Module.End (ZMod 2) F)) w = 0 := by
        have hEy : ((1 + (y : Module.End (ZMod 2) F) + (y : Module.End (ZMod 2) F) ^ 2 :
            Module.End (ZMod 2) F)) w = 0 := by
          change w + y w + (y ^ 2) w = 0
          exact hy0
        have hEx : ((1 + (x : Module.End (ZMod 2) F) + (x : Module.End (ZMod 2) F) ^ 2 :
            Module.End (ZMod 2) F))
            (((1 + (y : Module.End (ZMod 2) F) + (y : Module.End (ZMod 2) F) ^ 2 :
              Module.End (ZMod 2) F)) w) = 0 := by
          rw [hEy, map_zero]
        exact hEx
      rw [h5th, add_zero] at h
      simpa using h
    exact le_bot_iff.mp hle
  have case_i0 : W ⊓ fixSub (Subgroup.zpowers x) = W → ∀ w ∈ W, y w = w := by
    intro hC
    have hxpt : ∀ w ∈ W, x w = w := pointwise_of_eq hC
    have hcxc : ∀ w ∈ W, (c * x * c⁻¹) w = w := by
      intro w hw
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxpt _ (hciW w hw)]
      exact c.apply_symm_apply w
    rcases hcx with hcase | hcase
    · have hprod : ∀ w ∈ W, (x⁻¹ * (x * y)) w = w := by
        rw [hcase] at hcxc
        exact mul_pointwise (inv_pointwise hxpt) hcxc
      have heq : x⁻¹ * (x * y) = y := by group
      rw [heq] at hprod
      exact hprod
    · have hprod : ∀ w ∈ W, (x⁻¹ * (x * y⁻¹)) w = w := by
        rw [hcase] at hcxc
        exact mul_pointwise (inv_pointwise hxpt) hcxc
      have heq : x⁻¹ * (x * y⁻¹) = y⁻¹ := by group
      rw [heq] at hprod
      simpa using inv_pointwise hprod
  have case_i1 : W ⊓ fixSub (Subgroup.zpowers (x * y)) = W → ∀ w ∈ W, y w = w := by
    intro hC
    have hApt : ∀ w ∈ W, (x * y) w = w := pointwise_of_eq hC
    have hBpt : ∀ w ∈ W, (t * (x * y) * t⁻¹) w = w := pointwise_t hApt
    have hB_eq : t * (x * y) * t⁻¹ = x * y ^ 2 := by
      rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) by group, htx, hty2]
    rw [hB_eq] at hBpt
    have hprod : ∀ w ∈ W, ((x * y)⁻¹ * (x * y ^ 2)) w = w :=
      mul_pointwise (inv_pointwise hApt) hBpt
    have heq : (x * y)⁻¹ * (x * y ^ 2) = y := by group
    rw [heq] at hprod
    exact hprod
  have case_i2 : W ⊓ fixSub (Subgroup.zpowers (x * y ^ 2)) = W → ∀ w ∈ W, y w = w := by
    intro hC
    have hApt : ∀ w ∈ W, (x * y ^ 2) w = w := pointwise_of_eq hC
    have hBpt : ∀ w ∈ W, (t * (x * y ^ 2) * t⁻¹) w = w := pointwise_t hApt
    have hy4 : (y ^ 2) ^ 2 = y := by
      rw [← pow_mul, show 2 * 2 = 4 by norm_num, show (4 : ℕ) = 3 + 1 by norm_num,
        pow_add, hy3, pow_one, one_mul]
    have hB_eq : t * (x * y ^ 2) * t⁻¹ = x * y := by
      have h1 : t * (x * y ^ 2) * t⁻¹ =
          (t * x * t⁻¹) * (t * y * t⁻¹) * (t * y * t⁻¹) := by
        rw [pow_two]
        group
      rw [h1, htx, hty2, mul_assoc, ← pow_two, hy4]
    rw [hB_eq] at hBpt
    have hprod : ∀ w ∈ W, ((x * y ^ 2)⁻¹ * (x * y)) w = w :=
      mul_pointwise (inv_pointwise hApt) hBpt
    have heq : (x * y ^ 2)⁻¹ * (x * y) = y⁻¹ := by group
    rw [heq] at hprod
    simpa using inv_pointwise hprod
  have hy_contra : ¬ (∀ w ∈ W, y w = w) := by
    intro hall
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    exact hw0 (hfixfree w hw (hall w hw))
  have hdvdW : 6 ∣ Module.finrank (ZMod 2) W :=
    six_dvd_finrank_of_invariant hs hy3 hfixfree (le_refl W) hsW
  have hWpos : Module.finrank (ZMod 2) W ≠ 0 := by
    intro h0
    exact hWne ((Submodule.finrank_eq_zero (S := W)).mp h0)
  have hmain : 12 ≤ Module.finrank (ZMod 2) W := by
    by_contra hcon
    rw [not_le] at hcon
    have hdim : Module.finrank (ZMod 2) W = 6 := by
      obtain ⟨k, hk⟩ := hdvdW
      have hk1 : k = 1 := by
        have hpos := Nat.pos_of_ne_zero hWpos
        omega
      omega
    have hCx := fixed_eq_bot_or_top (y := y) (s := s) (b := x) hs hy3 hxs hsW hfixfree hdim
    have hCxy := fixed_eq_bot_or_top (y := y) (s := s) (b := x * y) hs hy3 hxys hsW hfixfree hdim
    have hCxy2 :=
      fixed_eq_bot_or_top (y := y) (s := s) (b := x * y ^ 2) hs hy3 hxy2s hsW hfixfree hdim
    rcases hCx with hCxbot | hCxW
    · rcases hCxy with hCxybot | hCxyW
      · rcases hCxy2 with hCxy2bot | hCxy2W
        · exact hallbot hCxbot hCxybot hCxy2bot
        · exact hy_contra (case_i2 hCxy2W)
      · exact hy_contra (case_i1 hCxyW)
    · exact hy_contra (case_i0 hCxW)
  rw [hWrange] at hmain
  exact hmain


end CFSG.LocalAnalysis.WeakClosure81

end

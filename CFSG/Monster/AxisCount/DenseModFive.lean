module

public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.Griess.ModFive.Lattice
import CFSG.Monster.Griess.ModFive.Torsion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Spin CFSG.Monster.Griess CFSG.Monster.Griess.ModFive
  CFSG.Monster.Visible Matrix

@[expose] noncomputable def DVec.res5 (v : Native.DVec) (k : ℕ) : ZMod 5 :=
  (v.D.getD k 0 : ZMod 5) * 3 ^ v.e
@[expose] def Cong5D (u v : Native.DVec) : Prop := ∀ k < 196884, DVec.res5 u k = DVec.res5 v k

theorem three_pow_mul_two_pow (n : ℕ) : (3 : ZMod 5) ^ n * 2 ^ n = 1 := by
  have h : (3 : ZMod 5) * 2 = 1 := by decide
  rw [← mul_pow, h, one_pow]

theorem intCast_div_two_pow_mem_R5 (a : ℤ) (e : ℕ) : (a : ℚ) / 2 ^ e ∈ R5 := by
  rw [div_eq_mul_inv, ← inv_pow]
  exact mul_mem (intCast_mem _ a) (pow_mem inv_two_mem_R5 e)

theorem div_sub_div_mem_D5 {a b : ℤ} {e f : ℕ}
    (h : (a : ZMod 5) * 3 ^ e = (b : ZMod 5) * 3 ^ f) :
    (a : ℚ) / 2 ^ e - (b : ℚ) / 2 ^ f ∈ D5 := by
  have h0 : ((a * 2 ^ f - b * 2 ^ e : ℤ) : ZMod 5) = 0 := by
    push_cast
    linear_combination (2 ^ e * 2 ^ f : ZMod 5) * h - (a : ZMod 5) * 2 ^ f *
      three_pow_mul_two_pow e + (b : ZMod 5) * 2 ^ e * three_pow_mul_two_pow f
  have hn : (5 : ℤ) ∣ a * 2 ^ f - b * 2 ^ e := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).1 h0
  have hq : (a : ℚ) / 2 ^ e - (b : ℚ) / 2 ^ f =
      ((a * 2 ^ f - b * 2 ^ e : ℤ) : ℚ) * ((2 : ℚ)⁻¹ ^ e * (2 : ℚ)⁻¹ ^ f) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), inv_pow, inv_pow, ← mul_inv,
      div_eq_mul_inv]
    push_cast
    ring
  rw [hq]
  exact mul_mem_D5' ((intCast_mem_D5_iff _).2 hn)
    (mul_mem (pow_mem inv_two_mem_R5 e) (pow_mem inv_two_mem_R5 f))

theorem res_eq_of_div_eq {a b : ℤ} {e f : ℕ} (h : (a : ℚ) / 2 ^ e = (b : ℚ) / 2 ^ f) :
    (a : ZMod 5) * 3 ^ e = (b : ZMod 5) * 3 ^ f := by
  rw [div_eq_div_iff (by positivity) (by positivity)] at h
  have hz : a * 2 ^ f = b * 2 ^ e := by exact_mod_cast h
  have hz5 := congrArg (Int.cast : ℤ → ZMod 5) hz
  push_cast at hz5
  linear_combination (3 ^ e * 3 ^ f : ZMod 5) * hz5 - (a : ZMod 5) * 3 ^ e *
    three_pow_mul_two_pow f + (b : ZMod 5) * 3 ^ f * three_pow_mul_two_pow e

theorem aIdx_lt_300 (i j : Fin 24) : Native.aIdx i j < 300 :=
  (Native.aIdx_spec i j i.2 j.2).1

theorem posOf_add_lt (c : ShortIdx) : 300 + posOf c < 196884 := by
  have := posOf_lt c
  omega

theorem rowOf_idx_lt (s : SpinIdx) (j : Fin 24) : 98580 + 24 * rowOf s + j < 196884 := by
  have := rowOf_lt s
  have := j.2
  omega

theorem int5_interp (v : Native.DVec) : ModFive.Int5 (interp v) :=
  ⟨fun _ _ => intCast_div_two_pow_mem_R5 _ _, fun _ => intCast_div_two_pow_mem_R5 _ _,
    fun _ _ => intCast_div_two_pow_mem_R5 _ _⟩

theorem cf_sub_mem_D5 {u v : Native.DVec} (h : Cong5D u v) {k : ℕ} (hk : k < 196884) :
    (5 : ℚ)⁻¹ * (cf u k - cf v k) ∈ R5 :=
  mem_D5_iff_inv_mul.1 (div_sub_div_mem_D5 (h k hk))

theorem cong5_interp_of_cong5D {u v : Native.DVec}
    (h : Cong5D u v) : ModFive.Cong5 (interp u) (interp v) :=
  ⟨int5_interp u, int5_interp v,
    ⟨fun i j => cf_sub_mem_D5 h (by have := aIdx_lt_300 i j; omega),
      fun c => cf_sub_mem_D5 h (posOf_add_lt c),
      fun s j => cf_sub_mem_D5 h (rowOf_idx_lt s j)⟩⟩

theorem cf_eq_of_interp_eq {u v : Native.DVec}
    (h : interp u = interp v) {k : ℕ} (hk : k < 196884) : cf u k = cf v k := by
  by_cases h1 : k < 300
  · obtain ⟨a1, a2⟩ := aPos_lt k h1
    have hidx : Native.aIdx (finOf (Native.aPos k).1) (finOf (Native.aPos k).2) = k := by
      rw [finOf_val _ a1, finOf_val _ a2, aIdx_aPos k h1]
    have e := congrFun (congrFun (congrArg (fun x : SpaceB => (x.1 : Matrix (Fin 24) (Fin 24) ℚ))
      h) (finOf (Native.aPos k).1)) (finOf (Native.aPos k).2)
    rw [← hidx]
    exact e
  by_cases h2 : k < 98580
  · have hp : k - 300 < 98280 := by omega
    have e := congrFun (congrArg (fun x : SpaceB => x.2.1) h) (shortOf ⟨k - 300, hp⟩)
    have hidx : 300 + posOf (shortOf ⟨k - 300, hp⟩) = k := by
      rw [posOf_shortOf]
      change 300 + (k - 300) = k
      omega
    rw [← hidx]
    exact e
  · have hr : (k - 98580) / 24 < 4096 := by omega
    have hj : (k - 98580) % 24 < 24 := Nat.mod_lt _ (by norm_num)
    have e := congrFun (congrFun (congrArg (fun x : SpaceB => x.2.2) h)
      (spinOfRow ((k - 98580) / 24))) (finOf ((k - 98580) % 24))
    have hidx : 98580 + 24 * rowOf (spinOfRow ((k - 98580) / 24)) +
        (finOf ((k - 98580) % 24) : ℕ) = k := by
      rw [rowOf_spinOfRow hr, finOf_val _ hj]
      omega
    rw [← hidx]
    exact e

theorem res5_eq_of_cf_eq {u v : Native.DVec} {k : ℕ} (h : cf u k = cf v k) :
    DVec.res5 u k = DVec.res5 v k :=
  res_eq_of_div_eq h

theorem toLin_mem_BR_iff (g : Native.Gen) (u : SpaceB) : g.toLin u ∈ BR ↔ u ∈ BR := by
  cases g with
  | rho q => exact theta_mem_BR_iff _
  | perm arr => exact theta_mem_BR_iff _
  | sign a => exact theta_mem_BR_iff _
  | xi => exact theta_mem_BR_iff _
  | tau => exact tauB_mem_BR_iff

theorem wordLin_mem_BR_iff (w : List Native.Gen) (u : SpaceB) : wordLin w u ∈ BR ↔ u ∈ BR := by
  induction w generalizing u with
  | nil => exact Iff.rfl
  | cons g w ih => rw [wordLin_apply_cons, ih, toLin_mem_BR_iff]

theorem wordLin_inv_mem_BR_iff (w : List Native.Gen) (u : SpaceB) :
    (wordLin w)⁻¹ u ∈ BR ↔ u ∈ BR := by
  change (wordLin w).symm u ∈ BR ↔ u ∈ BR
  rw [← wordLin_mem_BR_iff w, LinearEquiv.apply_symm_apply]

theorem int5_map_of_BR {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : ∀ u ∈ BR, f u ∈ BR) {x : SpaceB}
    (hx : ModFive.Int5 x) : ModFive.Int5 (f x) := by
  change f x ∈ L5
  rw [← basisB.sum_repr x, map_sum]
  refine sum_mem fun k _ => ?_
  rw [map_smul]
  obtain ⟨h1, h2, h3⟩ := mem_BR_iff.1 (hf _ (Submodule.subset_span ⟨k, rfl⟩))
  exact smul_mem_L5 (basisB_repr_mem_R5 hx k)
    ⟨fun i j => dyadic_le_R5 (h1 i j), fun c => dyadic_le_R5 (h2 c),
      fun j i => dyadic_le_R5 (h3 j i)⟩

theorem wordLin_int5 (w : List Native.Gen) {x : SpaceB} (hx : ModFive.Int5 x) :
    ModFive.Int5 (wordLin w x) :=
  int5_map_of_BR (fun u hu => (wordLin_mem_BR_iff w u).2 hu) hx

theorem wordLin_inv_int5 (w : List Native.Gen) {x : SpaceB} (hx : ModFive.Int5 x) :
    ModFive.Int5 ((wordLin w)⁻¹ x) :=
  int5_map_of_BR (fun u hu => (wordLin_inv_mem_BR_iff w u).2 hu) hx

theorem cong5_map {f : SpaceB ≃ₗ[ℚ] SpaceB} (hf : ∀ x, ModFive.Int5 x → ModFive.Int5 (f x))
    {u v : SpaceB} (h : ModFive.Cong5 u v) : ModFive.Cong5 (f u) (f v) :=
  ⟨hf _ h.1, hf _ h.2.1, by
    rw [← map_sub, ← LinearEquiv.map_smul]
    exact hf _ h.2.2⟩

theorem wordLin_apply_ne_of_res5_ne {w₁ w₂ : List Native.Gen}
    (h₁ : ∀ g ∈ w₁, g.validB = true) (h₂ : ∀ g ∈ w₂, g.validB = true) {v : Native.DVec} {k : ℕ}
    (hk : k < 196884)
    (h : DVec.res5 (Native.evalWord w₁ v) k ≠ DVec.res5 (Native.evalWord w₂ v) k) :
    wordLin w₁ (interp v) ≠ wordLin w₂ (interp v) := fun e => by
  rw [← evalWord_sound w₁ h₁, ← evalWord_sound w₂ h₂] at e
  exact h (res5_eq_of_cf_eq (cf_eq_of_interp_eq e hk))

theorem wordLin_ne_of_res5_ne {w₁ w₂ : List Native.Gen}
    (h₁ : ∀ g ∈ w₁, g.validB = true) (h₂ : ∀ g ∈ w₂, g.validB = true) {v : Native.DVec} {k : ℕ}
    (hk : k < 196884)
    (h : DVec.res5 (Native.evalWord w₁ v) k ≠ DVec.res5 (Native.evalWord w₂ v) k) :
    wordLin w₁ ≠ wordLin w₂ := fun e =>
  wordLin_apply_ne_of_res5_ne h₁ h₂ hk h (by rw [e])

end CFSG.Monster.AxisCount

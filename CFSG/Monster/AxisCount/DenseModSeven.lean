module

public import CFSG.Monster.AxisCount.DenseModFive
public import CFSG.Monster.AxisCount.HSIdentAxis
public import CFSG.Monster.Griess.ModSevenAxis
import CFSG.Monster.Griess.ModFive.Torsion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.AxisCount

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Griess
  CFSG.Monster.Griess.ModP CFSG.Monster.B.Short Matrix

@[expose] noncomputable def DVec.res7 (v : Native.DVec) (k : ℕ) : ZMod 7 :=
  (v.D.getD k 0 : ZMod 7) * 4 ^ v.e

@[expose] def Cong7D (u v : Native.DVec) : Prop := ∀ k < 196884, DVec.res7 u k = DVec.res7 v k

theorem four_pow_mul_two_pow (n : ℕ) : (4 : ZMod 7) ^ n * 2 ^ n = 1 := by
  have h : (4 : ZMod 7) * 2 = 1 := by decide
  rw [← mul_pow, h, one_pow]

theorem div_sub_div_div_seven_mem {a b : ℤ} {e f : ℕ}
    (h : (a : ZMod 7) * 4 ^ e = (b : ZMod 7) * 4 ^ f) :
    ((a : ℚ) / 2 ^ e - (b : ℚ) / 2 ^ f) / 7 ∈ ratLocal 7 := by
  have h0 : ((a * 2 ^ f - b * 2 ^ e : ℤ) : ZMod 7) = 0 := by
    push_cast
    linear_combination (2 ^ e * 2 ^ f : ZMod 7) * h - (a : ZMod 7) * 2 ^ f *
      four_pow_mul_two_pow e + (b : ZMod 7) * 2 ^ e * four_pow_mul_two_pow f
  obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).1 h0
  have hm' : (a : ℚ) * 2 ^ f - b * 2 ^ e = 7 * m := by exact_mod_cast hm
  have e1 : ((a : ℚ) / 2 ^ e - (b : ℚ) / 2 ^ f) / 7 =
      ((a : ℚ) * 2 ^ f - b * 2 ^ e) / 7 * ((2 : ℚ)⁻¹ ^ e * (2 : ℚ)⁻¹ ^ f) := by
    rw [inv_pow, inv_pow]
    field_simp
  have h2 : (2 : ℚ)⁻¹ ∈ ratLocal 7 := by
    have h := inv_natCast_mem_ratLocal 7 (n := 2) (by norm_num)
    exact_mod_cast h
  rw [e1, hm', mul_div_cancel_left₀ _ (by norm_num : (7 : ℚ) ≠ 0)]
  exact mul_mem (intCast_mem _ m) (mul_mem (pow_mem h2 e) (pow_mem h2 f))

theorem cf_sub_div_seven_mem {u v : Native.DVec} (h : Cong7D u v) {k : ℕ} (hk : k < 196884) :
    (cf u k - cf v k) / 7 ∈ ratLocal 7 :=
  div_sub_div_div_seven_mem (h k hk)

theorem sub_mem_LatP_of_cong7D {u v : Native.DVec}
    (h : Cong7D u v) : interp u - interp v ∈ LatP 7 1 := by
  refine mem_LatP.2 fun i => ?_
  rw [pow_one, Nat.cast_ofNat]
  rcases i with z | c | ⟨s, j⟩
  · rw [ModFive.basisB_repr_inl]
    induction z using Sym2.ind with
    | h i j =>
      rw [symEntry_mk]
      exact cf_sub_div_seven_mem h (by have := aIdx_lt_300 i j; omega)
  · rw [ModFive.basisB_repr_inr_inl]
    exact cf_sub_div_seven_mem h (posOf_add_lt c)
  · rw [ModFive.basisB_repr_inr_inr]
    exact cf_sub_div_seven_mem h (rowOf_idx_lt s j)

theorem wordLin_axis_eq_of_cong7D {w₁ w₂ : List Native.Gen}
    (hw₁ : ∀ g ∈ w₁, g.validB = true) (hw₂ : ∀ g ∈ w₂, g.validB = true) {d₁ d₂ : Native.DVec}
    {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁)) (hr₂ : IsShortCoord (coordOf r₂))
    (hd₁ : interp d₁ = axis r₁) (hd₂ : interp d₂ = axis r₂)
    (h : Cong7D (Native.evalWord w₁ d₁) (Native.evalWord w₂ d₂)) :
    wordLin w₁ (axis r₁) = wordLin w₂ (axis r₂) := by
  have hL := sub_mem_LatP_of_cong7D h
  rw [evalWord_sound w₁ hw₁, evalWord_sound w₂ hw₂, hd₁, hd₂] at hL
  exact eq_axis_of_sub_mem_LatP (p := 7) (by norm_num)
    (Generated.Gmat_le_AutO (wordLin_mem_Gmat w₁)) (Generated.Gmat_le_AutO (wordLin_mem_Gmat w₂))
    (fun x hx => (wordLin_mem_BR_iff w₁ x).2 hx) hr₁ hr₂ hL

theorem exists_axis_of_axisP_or_axisM {d : Native.DVec}
    (hd : d = HS.axisP ∨ d = HS.axisM) : ∃ r : Q, IsShortCoord (coordOf r) ∧ interp d = axis r := by
  rcases hd with rfl | rfl
  · exact ⟨rStar, isShortCoord_rStar, HS.interp_axisP⟩
  · exact ⟨zQ * rStar, isShortCoord_zQ_mul isShortCoord_rStar, HS.interp_axisM⟩

theorem wordLin_interp_eq_of_cong7D {w₁ w₂ : List Native.Gen}
    (hw₁ : ∀ g ∈ w₁, g.validB = true) (hw₂ : ∀ g ∈ w₂, g.validB = true) {d₁ d₂ : Native.DVec}
    (hd₁ : d₁ = HS.axisP ∨ d₁ = HS.axisM) (hd₂ : d₂ = HS.axisP ∨ d₂ = HS.axisM)
    (h : Cong7D (Native.evalWord w₁ d₁) (Native.evalWord w₂ d₂)) :
    wordLin w₁ (interp d₁) = wordLin w₂ (interp d₂) := by
  obtain ⟨r₁, hr₁, e₁⟩ := exists_axis_of_axisP_or_axisM hd₁
  obtain ⟨r₂, hr₂, e₂⟩ := exists_axis_of_axisP_or_axisM hd₂
  rw [e₁, e₂]
  exact wordLin_axis_eq_of_cong7D hw₁ hw₂ hr₁ hr₂ e₁ e₂ h

end CFSG.Monster.AxisCount

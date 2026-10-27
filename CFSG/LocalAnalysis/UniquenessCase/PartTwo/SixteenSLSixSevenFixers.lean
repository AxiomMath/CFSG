module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeTwoLn
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3FixSevenA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3FixSevenB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped Matrix
open CFSG.Quasithin CFSG.Open Subgroup

theorem s168e3_ln_fix_seven_two {n : ℕ} (hn : n = 6 ∨ n = 7) (u v : Fin n → ZMod 2) :
    ∃ B : GL (Fin n) (ZMod 2), orderOf B = 7 ∧
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u ∧
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v := by
  classical
  let f : Fin 0 → Fin n → ZMod 2 := fun i => Fin.elim0 i
  let g : Fin 2 → Fin n → ZMod 2 := fun i => if i = 0 then u else v
  have hcard : Fintype.card (Fin 2) + Fintype.card (Fin 0) ≤ 3 := by simp
  obtain ⟨s, hsord, hsv, -⟩ :=
    s16t3_model_exists_fix_seven hn (ι := Fin 2) (κ := Fin 0) g f hcard
  have hsu : s u = u := by simpa [g] using hsv 0
  have hsv' : s v = v := by simpa [g] using hsv 1
  obtain ⟨gSL, hgord, hgmul⟩ := s16t3_sl_of_linearEquiv s
  refine ⟨Matrix.SpecialLinearGroup.toGL gSL, ?_, ?_, ?_⟩
  · rw [orderOf_injective Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective gSL]
    exact hgord.trans hsord
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hgmul, hsu]
  · rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hgmul, hsv']

theorem s168e3_ln_fix_seven_dual {n : ℕ} (hn : n = 6 ∨ n = 7) (u w : Fin n → ZMod 2) :
    ∃ B : GL (Fin n) (ZMod 2), orderOf B = 7 ∧
      (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ u = u ∧
      ((B : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ w = w := by
  classical
  let f : Fin 1 → Fin n → ZMod 2 := fun _ => w
  let g : Fin 1 → Fin n → ZMod 2 := fun _ => u
  have hcard : Fintype.card (Fin 1) + Fintype.card (Fin 1) ≤ 3 := by simp
  obtain ⟨s, hsord, hsv, hsf⟩ :=
    s16t3_model_exists_fix_seven hn (ι := Fin 1) (κ := Fin 1) g f hcard
  have hsu : s u = u := by simpa using hsv 0
  have hsfw : ∀ z : Fin n → ZMod 2, w ⬝ᵥ (s z) = w ⬝ᵥ z := by
    intro z
    simpa using hsf 0 z
  obtain ⟨gSL, hgord, hgmul⟩ := s16t3_sl_of_linearEquiv s
  have hcoe : ((Matrix.SpecialLinearGroup.toGL gSL : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = (gSL : Matrix (Fin n) (Fin n) (ZMod 2)) :=
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix gSL
  have hBmul : ∀ z : Fin n → ZMod 2,
      ((Matrix.SpecialLinearGroup.toGL gSL : GL (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z = s z := by
    intro z
    rw [hcoe, hgmul]
  refine ⟨Matrix.SpecialLinearGroup.toGL gSL, ?_, ?_, ?_⟩
  · rw [orderOf_injective Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective gSL]
    exact hgord.trans hsord
  · rw [hBmul, hsu]
  · have htrans : ∀ z : Fin n → ZMod 2,
        (((Matrix.SpecialLinearGroup.toGL gSL : GL (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ w) ⬝ᵥ z = w ⬝ᵥ z := by
      intro z
      calc
        (((Matrix.SpecialLinearGroup.toGL gSL : GL (Fin n) (ZMod 2)) :
            Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ w) ⬝ᵥ z
            = (w ᵥ* ((Matrix.SpecialLinearGroup.toGL gSL : GL (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2))) ⬝ᵥ z := by
                rw [Matrix.mulVec_transpose]
        _ = w ⬝ᵥ (((Matrix.SpecialLinearGroup.toGL gSL : GL (Fin n) (ZMod 2)) :
                Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ z) := by
                rw [← Matrix.dotProduct_mulVec]
        _ = w ⬝ᵥ z := by
                rw [hBmul z]
                exact hsfw z
    funext i
    have h := htrans (Pi.single i 1)
    simpa [dotProduct_single] using h

theorem s168e3_ln_fix_order_seven {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {n : ℕ} (hn : n = 6 ∨ n = 7)
    (hsum : SumOfNat (fun H U Z => BinaryNaturalSL H U Z n 1) H (⊤ : Subgroup W) ⊥ 2) :
    ∀ x : W, x ≠ 1 → ∃ b ∈ H, orderOf b = 7 ∧ b x = x :=
  s168e3_ln_fix_order_of (p := 7) (by rcases hn with rfl | rfl <;> norm_num) hsum
    (fun u v => s168e3_ln_fix_seven_two hn u v)
    (fun u w => s168e3_ln_fix_seven_dual hn u w)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

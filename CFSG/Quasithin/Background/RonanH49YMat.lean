module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix

abbrev YMat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 0]

abbrev tMat : Fin 3 → Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  ![!![1, 0, 0; 0, 0, 0; 0, 0, 0], !![0, 0, 0; 0, 1, 0; 0, 0, 0], !![1, 1, 0; 1, 1, 0; 0, 0, 0]]

theorem toAdd_yW : Multiplicative.toAdd yW = YMat := by
  decide

theorem tMat_injective : Function.Injective tMat := by
  have key : ∀ i j : Fin 3, tMat i = tMat j → i = j := by decide
  exact fun i j h => key i j h

theorem YMat_symm : YMat ᵀ = YMat := by
  decide

theorem tMat_symm (i : Fin 3) : (tMat i)ᵀ = tMat i := by
  have key : ∀ k : Fin 3, (tMat k)ᵀ = tMat k := by decide
  exact key i

theorem third_row_of_Y_stab {a b : Matrix (Fin 3) (Fin 3) (ZMod 2)} (ha : a.det ≠ 0)
    (hb : b.det ≠ 0) (h : a * YMat * bᵀ = YMat) :
    a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 2 2 = 1 := by
  have hu : IsUnit bᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.mpr hb
  have h2 : a * YMat = YMat * (bᵀ)⁻¹ := by
    have h' : a * YMat * bᵀ * (bᵀ)⁻¹ = YMat * (bᵀ)⁻¹ := by rw [h]
    simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one] using h'
  have hY2 : ∀ j : Fin 3, YMat 2 j = 0 := by decide
  have hrow : ∀ k : Fin 3, (a * YMat) 2 k = 0 := by
    intro k
    rw [h2, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [hY2 j, zero_mul]
  have e0 : a 2 1 = 0 := by
    have h0 := hrow 0
    simpa [Matrix.mul_apply, Fin.sum_univ_three, YMat] using h0
  have e1 : a 2 0 = 0 := by
    have h1 := hrow 1
    simpa [Matrix.mul_apply, Fin.sum_univ_three, YMat] using h1
  have e2 : a 2 2 = 1 := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (a 2 2) with h22 | h22
    · exfalso
      apply ha
      rw [Matrix.det_fin_three, e0, e1, h22]
      ring
    · exact h22
  exact ⟨e1, e0, e2⟩

theorem P2_of_Y_stab {a b : Matrix (Fin 3) (Fin 3) (ZMod 2)} (ha : a.det ≠ 0) (hb : b.det ≠ 0)
    (h : a * YMat * bᵀ = YMat) :
    (a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 2 2 = 1) ∧ (b 2 0 = 0 ∧ b 2 1 = 0 ∧ b 2 2 = 1) := by
  refine ⟨third_row_of_Y_stab ha hb h, third_row_of_Y_stab hb ha ?_⟩
  have ht : (a * YMat * bᵀ)ᵀ = YMatᵀ := by rw [h]
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, YMat_symm, Matrix.mul_assoc]
    using ht

theorem Y_stab_param : ∀ p q u r s w p' q' u' r' s' w' : ZMod 2,
    !![p, q, u; r, s, w; 0, 0, 1] * YMat * (!![p', q', u'; r', s', w'; 0, 0, 1])ᵀ = YMat →
    ∀ i : Fin 3, ∃ j : Fin 3,
      !![p, q, u; r, s, w; 0, 0, 1] * tMat i * (!![p', q', u'; r', s', w'; 0, 0, 1])ᵀ = tMat j := by
  decide +kernel

theorem Y_stab_perm {a b : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (ha : a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 2 2 = 1) (hb : b 2 0 = 0 ∧ b 2 1 = 0 ∧ b 2 2 = 1)
    (h : a * YMat * bᵀ = YMat) : ∀ i : Fin 3, ∃ j : Fin 3, a * tMat i * bᵀ = tMat j := by
  have hA : !![a 0 0, a 0 1, a 0 2; a 1 0, a 1 1, a 1 2; 0, 0, 1] = a := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha.1, ha.2.1, ha.2.2]
  have hB : !![b 0 0, b 0 1, b 0 2; b 1 0, b 1 1, b 1 2; 0, 0, 1] = b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb.1, hb.2.1, hb.2.2]
  have key := Y_stab_param (a 0 0) (a 0 1) (a 0 2) (a 1 0) (a 1 1) (a 1 2)
    (b 0 0) (b 0 1) (b 0 2) (b 1 0) (b 1 1) (b 1 2) (by rw [hA, hB]; exact h)
  rw [hA, hB] at key
  exact key

theorem Y_stab_kernel_param : ∀ p q u r s w p' q' u' r' s' w' : ZMod 2,
    !![p, q, u; r, s, w; 0, 0, 1] * tMat 0 * (!![p', q', u'; r', s', w'; 0, 0, 1])ᵀ = tMat 0 →
    !![p, q, u; r, s, w; 0, 0, 1] * tMat 1 * (!![p', q', u'; r', s', w'; 0, 0, 1])ᵀ = tMat 1 →
    (p = 1 ∧ q = 0 ∧ r = 0 ∧ s = 1) ∧ (p' = 1 ∧ q' = 0 ∧ r' = 0 ∧ s' = 1) := by
  decide +kernel

theorem Y_stab_kernel {a b : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (ha : a 2 0 = 0 ∧ a 2 1 = 0 ∧ a 2 2 = 1) (hb : b 2 0 = 0 ∧ b 2 1 = 0 ∧ b 2 2 = 1)
    (h : a * YMat * bᵀ = YMat) (h0 : a * tMat 0 * bᵀ = tMat 0) (h1 : a * tMat 1 * bᵀ = tMat 1) :
    (∃ x y : ZMod 2, a = axMat x y) ∧ (∃ x y : ZMod 2, b = axMat x y) := by
  have hA : !![a 0 0, a 0 1, a 0 2; a 1 0, a 1 1, a 1 2; 0, 0, 1] = a := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha.1, ha.2.1, ha.2.2]
  have hB : !![b 0 0, b 0 1, b 0 2; b 1 0, b 1 1, b 1 2; 0, 0, 1] = b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb.1, hb.2.1, hb.2.2]
  obtain ⟨⟨hp, hq, hr, hs⟩, ⟨hp', hq', hr', hs'⟩⟩ :=
    Y_stab_kernel_param (a 0 0) (a 0 1) (a 0 2) (a 1 0) (a 1 1) (a 1 2)
      (b 0 0) (b 0 1) (b 0 2) (b 1 0) (b 1 1) (b 1 2)
      (by rw [hA, hB]; exact h0) (by rw [hA, hB]; exact h1)
  have hA' : a = axMat (a 0 2) (a 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [axMat, ha.1, ha.2.1, ha.2.2, hp, hq, hr, hs]
  have hB' : b = axMat (b 0 2) (b 1 2) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [axMat, hb.1, hb.2.1, hb.2.2, hp', hq', hr', hs']
  exact ⟨⟨_, _, hA'⟩, ⟨_, _, hB'⟩⟩

theorem axMat_stab (x y x' y' : ZMod 2) :
    axMat x y * YMat * (axMat x' y')ᵀ = YMat ∧
      ∀ i : Fin 3, axMat x y * tMat i * (axMat x' y')ᵀ = tMat i := by
  revert x y x' y'
  decide

theorem Y_stab_surj_key : ∀ f : Fin 3 → Fin 3, Function.Injective f → ∃ p q r s : ZMod 2,
    ((!![p, q, 0; r, s, 0; 0, 0, 1]) 2 0 = 0 ∧ (!![p, q, 0; r, s, 0; 0, 0, 1]) 2 1 = 0 ∧
      (!![p, q, 0; r, s, 0; 0, 0, 1]) 2 2 = 1) ∧
    (!![p, q, 0; r, s, 0; 0, 0, 1]).det ≠ 0 ∧
    !![p, q, 0; r, s, 0; 0, 0, 1] * YMat * (!![p, q, 0; r, s, 0; 0, 0, 1])ᵀ = YMat ∧
    ∀ i : Fin 3, !![p, q, 0; r, s, 0; 0, 0, 1] * tMat i * (!![p, q, 0; r, s, 0; 0, 0, 1])ᵀ =
      tMat (f i) := by
  decide +kernel

theorem Y_stab_surj (π : Equiv.Perm (Fin 3)) :
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), (A 2 0 = 0 ∧ A 2 1 = 0 ∧ A 2 2 = 1) ∧ A.det ≠ 0 ∧
      A * YMat * Aᵀ = YMat ∧ ∀ i : Fin 3, A * tMat i * Aᵀ = tMat (π i) := by
  obtain ⟨p, q, r, s, hk⟩ := Y_stab_surj_key π π.injective
  exact ⟨!![p, q, 0; r, s, 0; 0, 0, 1], hk⟩

end CFSG.Quasithin.RonanH49

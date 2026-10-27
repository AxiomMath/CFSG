module

public import CFSG.Fischer.F4
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.L1442

open CFSG.Fischer Matrix

local instance (priority := high) decEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

@[expose] def trF4 (x : F4) : ZMod 2 := ((x.code.val / 2 : ℕ) : ZMod 2)

theorem trF4_add (x y : F4) : trF4 (x + y) = trF4 x + trF4 y := by
  revert x y
  decide

theorem trF4_zero : trF4 0 = 0 := rfl

theorem F4_cases (a : F4) : a = 0 ∨ a = 1 ∨ a = F4.ω ∨ a = 1 + F4.ω := by
  revert a
  decide

theorem exists_trace_of_biadd {f : F4 → F4 → ZMod 2}
    (h₁ : ∀ a a' c, f (a + a') c = f a c + f a' c) (h₂ : ∀ a c c', f a (c + c') = f a c + f a c')
    (h₃ : ∀ a c, f (F4.ω * a) (F4.ω * F4.ω * c) = f a c) :
    ∃ l : F4, ∀ a c, f a c = trF4 (l * a * c) := by
  obtain ⟨l, hl1, hlω⟩ : ∃ l : F4, trF4 l = f 1 1 ∧ trF4 (l * F4.ω) = f 1 F4.ω := by
    generalize f 1 1 = u
    generalize f 1 F4.ω = w
    revert u w
    decide
  refine ⟨l, ?_⟩
  let d : F4 → F4 → ZMod 2 := fun a c => f a c + trF4 (l * a * c)
  have hd₁ : ∀ a a' c, d (a + a') c = d a c + d a' c := fun a a' c => by
    simp only [d, h₁, add_mul, mul_add, trF4_add]
    ring
  have hd₂ : ∀ a c c', d a (c + c') = d a c + d a c' := fun a c c' => by
    simp only [d, h₂, mul_add, trF4_add]
    ring
  have hd₃ : ∀ a c, d (F4.ω * a) (F4.ω * F4.ω * c) = d a c := fun a c => by
    have : l * (F4.ω * a) * (F4.ω * F4.ω * c) = l * a * c := by
      have hω : F4.ω * F4.ω * F4.ω = 1 := by decide
      calc l * (F4.ω * a) * (F4.ω * F4.ω * c) = l * a * c * (F4.ω * F4.ω * F4.ω) := by ring
        _ = l * a * c := by rw [hω, mul_one]
    simp only [d, h₃, this]
  have hd0 : ∀ c, d 0 c = 0 := fun c => by
    have h := hd₁ 0 0 c
    rw [add_zero] at h
    have : d 0 c + d 0 c = 0 := by rw [← two_mul]; exact mul_eq_zero_of_left (by decide) _
    rw [← h] at this
    exact this
  have hd0' : ∀ a, d a 0 = 0 := fun a => by
    have h := hd₂ a 0 0
    rw [add_zero] at h
    have : d a 0 + d a 0 = 0 := by rw [← two_mul]; exact mul_eq_zero_of_left (by decide) _
    rw [← h] at this
    exact this
  have hd11 : d 1 1 = 0 := by
    simp only [d, mul_one, hl1]
    exact CharTwo.add_self_eq_zero _
  have hd1ω : d 1 F4.ω = 0 := by
    simp only [d, mul_one, hlω]
    exact CharTwo.add_self_eq_zero _
  have hdω1 : d F4.ω 1 = 0 := by
    have h := hd₃ 1 F4.ω
    have e1 : F4.ω * 1 = F4.ω := by decide
    have e2 : F4.ω * F4.ω * F4.ω = 1 := by decide
    rw [e1, e2] at h
    rw [h, hd1ω]
  have hdωω : d F4.ω F4.ω = 0 := by
    have h := hd₃ 1 1
    have e1 : F4.ω * 1 = F4.ω := by decide
    have e2 : F4.ω * F4.ω * 1 = 1 + F4.ω := by decide
    rw [e1, e2, hd₂, hdω1, hd11, zero_add] at h
    exact h
  have hrow : ∀ a, d a 1 = 0 ∧ d a F4.ω = 0 := by
    intro a
    rcases F4_cases a with rfl | rfl | rfl | rfl
    · exact ⟨hd0 _, hd0 _⟩
    · exact ⟨hd11, hd1ω⟩
    · exact ⟨hdω1, hdωω⟩
    · rw [hd₁, hd₁, hd11, hd1ω, hdω1, hdωω]
      exact ⟨rfl, rfl⟩
  intro a c
  have hdac : d a c = 0 := by
    rcases F4_cases c with rfl | rfl | rfl | rfl
    · exact hd0' a
    · exact (hrow a).1
    · exact (hrow a).2
    · rw [hd₂, (hrow a).1, (hrow a).2, add_zero]
  have : f a c + trF4 (l * a * c) = 0 := hdac
  calc f a c = f a c + trF4 (l * a * c) + trF4 (l * a * c) := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = trF4 (l * a * c) := by rw [this, zero_add]

@[expose] def sl (a b c d : F4) (h : a * d - b * c = 1) : SpecialLinearGroup (Fin 2) F4 :=
  ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem coe_sl (a b c d : F4) (h : a * d - b * c = 1) :
    (sl a b c d h : Matrix (Fin 2) (Fin 2) F4) = !![a, b; c, d] := rfl

theorem f4_neg_eq_self (x : F4) : -x = x := rfl

theorem f4_sub_eq_add (x y : F4) : x - y = x + y := rfl

section Form

variable {q : Matrix (Fin 2) (Fin 2) F4 → ZMod 2}
  {b : Matrix (Fin 2) (Fin 2) F4 → Matrix (Fin 2) (Fin 2) F4 → ZMod 2}

theorem polar_eq (hq : ∀ X Y, q (X + Y) = q X + q Y + b X Y) (X Y : Matrix (Fin 2) (Fin 2) F4) :
    b X Y = q (X + Y) + q X + q Y := by
  rw [hq]
  calc b X Y = q X + q X + (q Y + q Y) + b X Y := by
        rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, zero_add]
    _ = q X + q Y + b X Y + q X + q Y := by ring

theorem exists_eq_trace_det (hq : ∀ X Y, q (X + Y) = q X + q Y + b X Y)
    (hb₁ : ∀ X X' Y, b (X + X') Y = b X Y + b X' Y) (hb₂ : ∀ X Y Y', b X (Y + Y') = b X Y + b X Y')
    (hinv : ∀ A B : SpecialLinearGroup (Fin 2) F4, ∀ X,
      q ((A : Matrix (Fin 2) (Fin 2) F4) * X * (B : Matrix (Fin 2) (Fin 2) F4)) = q X) :
    ∃ l : F4, ∀ X, q X = trF4 (l * X.det) := by
  have hL : ∀ (A : SpecialLinearGroup (Fin 2) F4) X,
      q ((A : Matrix (Fin 2) (Fin 2) F4) * X) = q X :=
    fun A X => by simpa using hinv A 1 X
  have hR : ∀ (B : SpecialLinearGroup (Fin 2) F4) X,
      q (X * (B : Matrix (Fin 2) (Fin 2) F4)) = q X :=
    fun B X => by simpa using hinv 1 B X
  have hbL : ∀ (A : SpecialLinearGroup (Fin 2) F4) X Y,
      b ((A : Matrix (Fin 2) (Fin 2) F4) * X) ((A : Matrix (Fin 2) (Fin 2) F4) * Y) = b X Y := by
    intro A X Y
    rw [polar_eq hq, polar_eq hq, ← Matrix.mul_add, hL, hL, hL]
  have hbR : ∀ (B : SpecialLinearGroup (Fin 2) F4) X Y,
      b (X * (B : Matrix (Fin 2) (Fin 2) F4)) (Y * (B : Matrix (Fin 2) (Fin 2) F4)) = b X Y := by
    intro B X Y
    rw [polar_eq hq, polar_eq hq, ← Matrix.add_mul, hR, hR, hR]
  have hq0 : q 0 = 0 := by
    have hb0 : b 0 0 = 0 := by
      have h := hb₂ 0 0 0
      rw [add_zero] at h
      have : b 0 0 + b 0 0 = 0 := CharTwo.add_self_eq_zero _
      rw [← h] at this
      exact this
    have h := hq 0 0
    rw [add_zero, hb0, add_zero] at h
    have : q 0 + q 0 = 0 := CharTwo.add_self_eq_zero _
    rw [← h] at this
    exact this
  have hrow : ∀ a c : F4, (a, c) ≠ (0, 0) → q !![a, c; 0, 0] = q !![1, 0; 0, 0] := by
    intro a c hac
    by_cases ha : a = 0
    · subst ha
      have hc : c ≠ 0 := fun hc => hac (by rw [hc])
      have h1 : (0 : F4) * 0 - c * c⁻¹ = 1 := by
        rw [mul_inv_cancel₀ hc, zero_mul, zero_sub, f4_neg_eq_self]
      have h2 := hR (sl 0 c c⁻¹ 0 h1) !![1, 0; 0, 0]
      rw [coe_sl] at h2
      rw [← h2]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    · have h1 : a * a⁻¹ - c * 0 = 1 := by rw [mul_inv_cancel₀ ha, mul_zero, sub_zero]
      have h2 := hR (sl a c 0 a⁻¹ h1) !![1, 0; 0, 0]
      rw [coe_sl] at h2
      rw [← h2]
      congr 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  have hκ0 : q !![1, 0; 0, 0] = 0 := by
    have key : ∀ X Y Z : Matrix (Fin 2) (Fin 2) F4, q (X + Y + Z) =
        q (X + Y) + q (X + Z) + q (Y + Z) + q X + q Y + q Z := by
      intro X Y Z
      rw [hq (X + Y) Z, hb₁, polar_eq hq X Z, polar_eq hq Y Z]
      linear_combination CharTwo.add_self_eq_zero (q Z)
    have k := key !![1, 0; 0, 0] !![0, 1; 0, 0] !![F4.ω, 0; 0, 0]
    have m1 : (!![1, 0; 0, 0] + !![0, 1; 0, 0] + !![F4.ω, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F4) =
        !![1 + F4.ω, 1; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have m2 : (!![1, 0; 0, 0] + !![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) F4) = !![1, 1; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have m3 : (!![1, 0; 0, 0] + !![F4.ω, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F4) =
        !![1 + F4.ω, 0; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have m4 : (!![0, 1; 0, 0] + !![F4.ω, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F4) =
        !![F4.ω, 1; 0, 0] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [m1, m2, m3, m4, hrow (1 + F4.ω) 1 (by decide), hrow 1 1 (by decide),
      hrow (1 + F4.ω) 0 (by decide), hrow F4.ω 1 (by decide), hrow 0 1 (by decide),
      hrow F4.ω 0 (by decide)] at k
    have h6 : ∀ x : ZMod 2, x = x + x + x + x + x + x → x = 0 := by decide
    exact h6 _ k
  have hrow0 : ∀ a c : F4, q !![a, c; 0, 0] = 0 := by
    intro a c
    by_cases hac : (a, c) = (0, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hac
      rw [show (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F4) = 0 by ext i j; fin_cases i <;>
        fin_cases j <;> rfl, hq0]
    · rw [hrow a c hac, hκ0]
  have hJ : (0 : F4) * 0 - 1 * 1 = 1 := by decide
  have hrow1 : ∀ a c : F4, q !![0, 0; a, c] = 0 := by
    intro a c
    have h := hL (sl 0 1 1 0 hJ) !![a, c; 0, 0]
    rw [coe_sl] at h
    rw [show (!![0, 0; a, c] : Matrix (Fin 2) (Fin 2) F4) = !![0, 1; 1, 0] * !![a, c; 0, 0] by
      ext i j; fin_cases i <;> fin_cases j <;> simp, h, hrow0]
  have hcol0 : ∀ a c : F4, q !![a, 0; c, 0] = 0 := by
    intro a c
    by_cases ha : a = 0
    · subst ha
      by_cases hc : c = 0
      · subst hc
        rw [show (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) F4) = 0 by ext i j; fin_cases i <;>
          fin_cases j <;> rfl, hq0]
      · have h1 : (0 : F4) * 0 - c⁻¹ * c = 1 := by
          rw [inv_mul_cancel₀ hc, zero_mul, zero_sub, f4_neg_eq_self]
        have h2 := hL (sl 0 c⁻¹ c 0 h1) !![1, 0; 0, 0]
        rw [coe_sl] at h2
        rw [show (!![0, 0; c, 0] : Matrix (Fin 2) (Fin 2) F4) =
          !![0, c⁻¹; c, 0] * !![1, 0; 0, 0] by ext i j; fin_cases i <;> fin_cases j <;> simp, h2,
          hκ0]
    · have h1 : a * a⁻¹ - 0 * c = 1 := by rw [mul_inv_cancel₀ ha, zero_mul, sub_zero]
      have h2 := hL (sl a 0 c a⁻¹ h1) !![1, 0; 0, 0]
      rw [coe_sl] at h2
      rw [show (!![a, 0; c, 0] : Matrix (Fin 2) (Fin 2) F4) =
        !![a, 0; c, a⁻¹] * !![1, 0; 0, 0] by ext i j; fin_cases i <;> fin_cases j <;> simp, h2,
        hκ0]
  have hcol1 : ∀ a c : F4, q !![0, a; 0, c] = 0 := by
    intro a c
    have h := hR (sl 0 1 1 0 hJ) !![a, 0; c, 0]
    rw [coe_sl] at h
    rw [show (!![0, a; 0, c] : Matrix (Fin 2) (Fin 2) F4) = !![a, 0; c, 0] * !![0, 1; 1, 0] by
      ext i j; fin_cases i <;> fin_cases j <;> simp, h, hcol0]
  let f : F4 → F4 → ZMod 2 := fun a c => b !![a, 0; 0, 0] !![0, 0; 0, c]
  have hf₁ : ∀ a a' c, f (a + a') c = f a c + f a' c := fun a a' c => by
    simp only [f]
    rw [← hb₁]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hf₂ : ∀ a c c', f a (c + c') = f a c + f a c' := fun a c c' => by
    simp only [f]
    rw [← hb₂]
    congr 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hD : F4.ω * (F4.ω * F4.ω) - 0 * 0 = 1 := by decide
  have hf₃ : ∀ a c, f (F4.ω * a) (F4.ω * F4.ω * c) = f a c := fun a c => by
    simp only [f]
    have h := hbL (sl F4.ω 0 0 (F4.ω * F4.ω) hD) !![a, 0; 0, 0] !![0, 0; 0, c]
    rw [coe_sl] at h
    rw [← h]
    congr 1
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp [mul_assoc]
  obtain ⟨l, hl⟩ := exists_trace_of_biadd hf₁ hf₂ hf₃
  refine ⟨l, fun X => ?_⟩
  have e1 : q X = b !![X 0 0, 0; 0, 0] !![0, 0; 0, X 1 1] +
      b !![0, X 0 1; 0, 0] !![0, 0; X 1 0, 0] := by
    have hsplit := hq !![X 0 0, X 0 1; 0, 0] !![0, 0; X 1 0, X 1 1]
    rw [show (!![X 0 0, X 0 1; 0, 0] + !![0, 0; X 1 0, X 1 1] : Matrix (Fin 2) (Fin 2) F4) = X by
      ext i j; fin_cases i <;> fin_cases j <;> simp] at hsplit
    rw [hsplit, hrow0, hrow1, zero_add, zero_add,
      show (!![X 0 0, X 0 1; 0, 0] : Matrix (Fin 2) (Fin 2) F4) =
        !![X 0 0, 0; 0, 0] + !![0, X 0 1; 0, 0] by ext i j; fin_cases i <;> fin_cases j <;> simp,
      show (!![0, 0; X 1 0, X 1 1] : Matrix (Fin 2) (Fin 2) F4) =
        !![0, 0; X 1 0, 0] + !![0, 0; 0, X 1 1] by ext i j; fin_cases i <;> fin_cases j <;> simp,
      hb₁, hb₂, hb₂]
    have c1 : b !![X 0 0, 0; 0, 0] !![0, 0; X 1 0, 0] = 0 := by
      rw [polar_eq hq, show (!![X 0 0, 0; 0, 0] + !![0, 0; X 1 0, 0] : Matrix (Fin 2) (Fin 2) F4) =
        !![X 0 0, 0; X 1 0, 0] by ext i j; fin_cases i <;> fin_cases j <;> simp, hcol0, hrow0,
        hrow1]
      rfl
    have c2 : b !![0, X 0 1; 0, 0] !![0, 0; 0, X 1 1] = 0 := by
      rw [polar_eq hq, show (!![0, X 0 1; 0, 0] + !![0, 0; 0, X 1 1] : Matrix (Fin 2) (Fin 2) F4) =
        !![0, X 0 1; 0, X 1 1] by ext i j; fin_cases i <;> fin_cases j <;> simp, hcol1, hrow0,
        hrow1]
      rfl
    rw [c1, c2]
    ring
  have e2 : b !![0, X 0 1; 0, 0] !![0, 0; X 1 0, 0] = f (X 0 1) (X 1 0) := by
    simp only [f]
    have h := hbR (sl 0 1 1 0 hJ) !![0, X 0 1; 0, 0] !![0, 0; X 1 0, 0]
    rw [coe_sl] at h
    rw [← h]
    congr 1
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [e1, e2]
  change f (X 0 0) (X 1 1) + f (X 0 1) (X 1 0) = _
  rw [hl, hl, ← trF4_add, Matrix.det_fin_two, f4_sub_eq_add]
  congr 1
  ring

end Form

theorem trace_det_smul (l : F4) (X : Matrix (Fin 2) (Fin 2) F4) :
    trF4 ((l * l) • X).det = trF4 (l * X.det) := by
  rw [Matrix.det_smul, Fintype.card_fin]
  congr 1
  have h4 : (l * l) ^ 2 = l := by rw [← sq]; exact F4.sq_sq l
  rw [h4]

end CFSG.Quasithin.H13.L1442

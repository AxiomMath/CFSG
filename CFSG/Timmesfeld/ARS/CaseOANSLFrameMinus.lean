module

public import CFSG.Timmesfeld.ARS.CaseOANSLFrameC
public import CFSG.Timmesfeld.RankTwo.LevisMinusNFrame

public section

open scoped commutatorElement
open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg CFSG.LieType.RootSystem
open CFSG.Timmesfeld.RankTwo
open Matrix

namespace CFSG.Timmesfeld.ARS.CaseOANSL

section ShiftB

variable {n : ℕ}

@[expose] def shiftB (γ : Fin (n + 2 - 1) → ℤ) : Fin (n - 1) → ℤ := fun j => γ ⟨j.val + 2, by omega⟩

theorem shiftB_add (γ δ : Fin (n + 2 - 1) → ℤ) : shiftB (γ + δ) = shiftB γ + shiftB δ := rfl

theorem shiftB_neg (γ : Fin (n + 2 - 1) → ℤ) : shiftB (-γ) = -shiftB γ := rfl

theorem shiftB_smul (a : ℕ) (γ : Fin (n + 2 - 1) → ℤ) : shiftB (a • γ) = a • shiftB γ := rfl

abbrev upB (k : Fin (n - 1)) : Fin (n + 2 - 1) := ⟨k.val + 2, by omega⟩

theorem shiftB_single_upB (k : Fin (n - 1)) :
    shiftB (Pi.single (upB k) 1 : Fin (n + 2 - 1) → ℤ) = Pi.single k 1 := by
  funext j
  simp only [shiftB, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem single_upB_zero (k : Fin (n - 1)) :
    (Pi.single (upB k) 1 : Fin (n + 2 - 1) → ℤ) ⟨0, by omega⟩ = 0 :=
  Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (0 : ℕ) ≠ k.val + 2 by omega)) 1

theorem single_upB_one (k : Fin (n - 1)) :
    (Pi.single (upB k) 1 : Fin (n + 2 - 1) → ℤ) ⟨1, by have := k.isLt; omega⟩ = 0 :=
  Pi.single_eq_of_ne (Fin.ne_of_val_ne (show (1 : ℕ) ≠ k.val + 2 by omega)) 1

theorem upB_succ (k : Fin (n - 1)) (hk : k.val + 1 < n - 1) :
    (⟨(upB k).val + 1, show k.val + 2 + 1 < n + 1 by omega⟩ : Fin (n + 2 - 1)) =
      upB ⟨k.val + 1, hk⟩ :=
  Fin.ext (show k.val + 2 + 1 = k.val + 1 + 2 by omega)

theorem node_casesB (hn : 1 ≤ n) (i : Fin (n + 2 - 1)) :
    i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ ∨ ∃ k : Fin (n - 1), i = upB k := by
  rcases i with ⟨_ | _ | i, hi⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨⟨i, by omega⟩, rfl⟩)

theorem cartanB_shift (k j : Fin (n - 1)) :
    cartanB (n + 2 - 1) (upB k) (upB j) = cartanB (n - 1) k j := by
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem sum_shiftB (hn : 2 ≤ n) (f : Fin (n + 2 - 1) → ℤ) (h0 : f ⟨0, by omega⟩ = 0)
    (h1 : f ⟨1, by omega⟩ = 0) : ∑ l, f l = ∑ j : Fin (n - 1), f (upB j) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show (∑ l : Fin (m + 2 + 2 - 1), f l) = ∑ l : Fin (m + 3), f l from rfl,
    Fin.sum_univ_succ, Fin.sum_univ_succ]
  have e0 : f (0 : Fin (m + 3)) = 0 := by simpa using h0
  have e1 : f (Fin.succ (0 : Fin (m + 2))) = 0 := by simpa using h1
  rw [e0, e1, zero_add, zero_add]
  exact Fintype.sum_equiv (finCongr (by omega)) _ _
    (fun j => congrArg f (Fin.ext (by simp)))

theorem shiftB_reflection (k : Fin (n - 1)) {γ : Fin (n + 2 - 1) → ℤ}
    (h0 : γ ⟨0, by have := k.isLt; omega⟩ = 0) (h1 : γ ⟨1, by have := k.isLt; omega⟩ = 0) :
    shiftB (reflection (cartanB (n + 2 - 1)) (upB k) γ) =
      reflection (cartanB (n - 1)) k (shiftB γ) := by
  have hn : 2 ≤ n := by have := k.isLt; omega
  rw [reflection_apply, reflection_apply]
  funext j
  simp only [shiftB, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  congr 1
  · rw [show (∑ l : Fin (n + 2 - 1), cartanB (n + 2 - 1) (upB k) l * γ l) =
        ∑ l : Fin (n + 2 - 1), cartanB (n + 2 - 1) (upB k) l * γ l from rfl,
      sum_shiftB hn _ (by rw [h0, mul_zero]) (by rw [h1, mul_zero])]
    exact Finset.sum_congr rfl fun l _ => by rw [cartanB_shift]
  · simp only [Pi.single_apply, Fin.ext_iff]
    split_ifs <;> omega

theorem toStdB_shiftB (a : Fin (n - 1)) {γ : Fin (n + 2 - 1) → ℤ}
    (h1 : γ ⟨1, by have := a.isLt; omega⟩ = 0) :
    toStdB (n - 1) (shiftB γ) a = toStdB (n + 2 - 1) γ (upB a) := by
  unfold toStdB shiftB
  by_cases ha : 0 < a.val
  · rw [dite_eq_left ha, dite_eq_left (show 0 < (upB a).val by simp)]
    exact congrArg (fun z => γ ⟨a.val + 2, by omega⟩ - z) (congrArg γ (Fin.ext (by simp; omega)))
  · rw [dite_eq_right ha, dite_eq_left (show 0 < (upB a).val by simp)]
    have e : γ ⟨(upB a).val - 1, by omega⟩ = 0 := by
      rw [← h1]
      exact congrArg γ (Fin.ext (by simp; omega))
    rw [e]

theorem toStdB_apply_zeroB {γ : Fin (n + 2 - 1) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0) :
    toStdB (n + 2 - 1) γ ⟨0, by omega⟩ = 0 := by
  unfold toStdB
  rw [dite_eq_right (lt_irrefl 0)]
  simpa using h0

theorem toStdB_apply_oneB (hn : 1 ≤ n) {γ : Fin (n + 2 - 1) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0)
    (h1 : γ ⟨1, by omega⟩ = 0) : toStdB (n + 2 - 1) γ ⟨1, by omega⟩ = 0 := by
  unfold toStdB
  rw [dite_eq_left Nat.one_pos]
  have e : γ ⟨1 - 1, by omega⟩ = 0 := h0
  rw [e, sub_zero]
  exact h1

theorem minusLong_shiftB (hn : 2 ≤ n) {γ : Fin (n + 2 - 1) → ℤ} (hγ : MinusLong (n + 2) γ)
    (h0 : γ ⟨0, by omega⟩ = 0) (h1 : γ ⟨1, by omega⟩ = 0) : MinusLong n (shiftB γ) := by
  obtain ⟨⟨i, j, s, t⟩, hij, h⟩ := hγ
  have e0 := toStdB_apply_zeroB h0
  have e1 := toStdB_apply_oneB (by omega) h0 h1
  rw [h] at e0 e1
  have hij' : i.val ≠ j.val := Fin.val_ne_of_ne hij
  have hs := boolSign_ne_zero s
  have ht := boolSign_ne_zero t
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff] at e0 e1
  have hi : 2 ≤ i.val ∧ 2 ≤ j.val := by
    constructor
    · by_contra hc
      split_ifs at e0 e1
      all_goals simp_all
      all_goals omega
    · by_contra hc
      split_ifs at e0 e1
      all_goals simp_all
      all_goals omega
  refine ⟨(⟨i.val - 2, by omega⟩, ⟨j.val - 2, by omega⟩, s, t),
    Fin.ne_of_val_ne (by simp only; omega), funext fun a => ?_⟩
  rw [toStdB_shiftB a h1, h]
  simp only [Pi.add_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem minusShort_shiftB (hn : 2 ≤ n) {γ : Fin (n + 2 - 1) → ℤ} (hγ : MinusShort (n + 2) γ)
    (h0 : γ ⟨0, by omega⟩ = 0) (h1 : γ ⟨1, by omega⟩ = 0) : MinusShort n (shiftB γ) := by
  obtain ⟨⟨i, s⟩, h⟩ := hγ
  have e0 := toStdB_apply_zeroB h0
  have e1 := toStdB_apply_oneB (by omega) h0 h1
  rw [h] at e0 e1
  have hs := boolSign_ne_zero s
  simp only [Pi.single_apply, Fin.ext_iff] at e0 e1
  have hi : 2 ≤ i.val := by
    by_contra hc
    split_ifs at e0 e1
    all_goals simp_all
    all_goals omega
  refine ⟨(⟨i.val - 2, by omega⟩, s), funext fun a => ?_⟩
  rw [toStdB_shiftB a h1, h]
  simp only [Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem reflectionB_apply_zero (k : Fin (n - 1)) {γ : Fin (n + 2 - 1) → ℤ}
    (h0 : γ ⟨0, by omega⟩ = 0) :
    reflection (cartanB (n + 2 - 1)) (upB k) γ ⟨0, by omega⟩ = 0 := by
  rw [reflection_apply_of_ne _ (Fin.ne_of_val_ne (by simp)) γ, h0]

theorem reflectionB_apply_one (k : Fin (n - 1)) {γ : Fin (n + 2 - 1) → ℤ}
    (h1 : γ ⟨1, by have := k.isLt; omega⟩ = 0) :
    reflection (cartanB (n + 2 - 1)) (upB k) γ ⟨1, by have := k.isLt; omega⟩ = 0 := by
  rw [reflection_apply_of_ne _ (Fin.ne_of_val_ne (by simp)) γ, h1]

theorem minusLong_neg' {γ : Fin (n - 1) → ℤ} (h : MinusLong n γ) : MinusLong n (-γ) := by
  obtain ⟨⟨i, j, s, t⟩, hij, h⟩ := h
  refine .of_eq hij (!s) (!t) ?_
  rw [toStdB_neg, h, boolSign_not, boolSign_not, Pi.single_neg, Pi.single_neg, neg_add]

theorem node_casesM {m : ℕ} (i : Fin (m + 4 + 2 - 1)) :
    i = ⟨0, by omega⟩ ∨ i = ⟨1, by omega⟩ ∨ ∃ k : Fin (m + 4 - 1), i = upB k :=
  node_casesB (by omega) i

end ShiftB

section FrameM

variable {G : Type} [Group G] {m : ℕ} {F : Type} [Field F] {b c : F}

abbrev d0 (m : ℕ) : Fin (m + 4 + 2 - 1) → ℤ := Pi.single ⟨0, by omega⟩ 1

abbrev d1 (m : ℕ) : Fin (m + 4 + 2 - 1) → ℤ := Pi.single ⟨1, by omega⟩ 1

abbrev d2 (m : ℕ) : Fin (m + 4 + 2 - 1) → ℤ := Pi.single ⟨2, by omega⟩ 1

@[simp] theorem d0_apply (k : Fin (m + 4 + 2 - 1)) : d0 m k = if k.val = 0 then 1 else 0 := by
  unfold d0
  rw [Pi.single_apply]
  exact if_congr Fin.ext_iff rfl rfl

@[simp] theorem d1_apply (k : Fin (m + 4 + 2 - 1)) : d1 m k = if k.val = 1 then 1 else 0 := by
  unfold d1
  rw [Pi.single_apply]
  exact if_congr Fin.ext_iff rfl rfl

@[simp] theorem d2_apply (k : Fin (m + 4 + 2 - 1)) : d2 m k = if k.val = 2 then 1 else 0 := by
  unfold d2
  rw [Pi.single_apply]
  exact if_congr Fin.ext_iff rfl rfl

@[expose] noncomputable def oaPsiL (Θ : spinGroup (quadMinus (m + 4) F b c) →* G)
    (φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G) : (Fin (m + 4 + 2 - 1) → ℤ) → F → G :=
  fun γ x =>
  if γ = d0 m then φ₀ (tv 0 1 x) else if γ = -d0 m then φ₀ (tv 1 0 x)
  else if γ = d1 m then φ₀ (tv 1 2 x) else if γ = -d1 m then φ₀ (tv 2 1 x)
  else if γ = d0 m + d1 m then φ₀ (tv 0 2 x) else if γ = -(d0 m + d1 m) then φ₀ (tv 2 0 x)
  else if γ = d1 m + d2 m then φ₁ (tv 0 2 x) else if γ = -(d1 m + d2 m) then φ₁ (tv 2 0 x)
  else Θ (minusXL (m + 4) b c (shiftB γ) x)

@[expose] noncomputable def oaPsiS (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Θ : spinGroup (quadMinus (m + 4) F b c) →* G) :
    (Fin (m + 4 + 2 - 1) → ℤ) → (Fin 2 → F) → G :=
  fun γ p => Θ (minusXS (m + 4) hirr (shiftB γ) p)

variable (Θ : spinGroup (quadMinus (m + 4) F b c) →* G) (φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G)

omit [Field F] in
theorem ne_of_apply_neB {v w : Fin (m + 4 + 2 - 1) → ℤ} (k : Fin (m + 4 + 2 - 1))
    (h : v k ≠ w k) : v ≠ w :=
  fun e => h (congrFun e k)

theorem oaPsiL_d0 (x : F) : oaPsiL Θ φ₀ φ₁ (d0 m) x = φ₀ (tv 0 1 x) := by
  simp [oaPsiL]

theorem oaPsiL_nd0 (x : F) : oaPsiL Θ φ₀ φ₁ (-d0 m) x = φ₀ (tv 1 0 x) := by
  rw [oaPsiL, ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsiL_d1 (x : F) : oaPsiL Θ φ₀ φ₁ (d1 m) x = φ₀ (tv 1 2 x) := by
  rw [oaPsiL, ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsiL_nd1 (x : F) : oaPsiL Θ φ₀ φ₁ (-d1 m) x = φ₀ (tv 2 1 x) := by
  rw [oaPsiL, ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsiL_d01 (x : F) : oaPsiL Θ φ₀ φ₁ (d0 m + d1 m) x = φ₀ (tv 0 2 x) := by
  rw [oaPsiL, ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsiL_nd01 (x : F) : oaPsiL Θ φ₀ φ₁ (-(d0 m + d1 m)) x = φ₀ (tv 2 0 x) := by
  rw [oaPsiL, ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsiL_d12 (x : F) : oaPsiL Θ φ₀ φ₁ (d1 m + d2 m) x = φ₁ (tv 0 2 x) := by
  rw [oaPsiL, ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨2, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsiL_nd12 (x : F) : oaPsiL Θ φ₀ φ₁ (-(d1 m + d2 m)) x = φ₁ (tv 2 0 x) := by
  rw [oaPsiL, ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨2, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨0, by omega⟩ (by simp)),
    ite_eq_right (ne_of_apply_neB ⟨1, by omega⟩ (by simp)), ite_eq_left rfl]

theorem oaPsiL_of_last {γ : Fin (m + 4 + 2 - 1) → ℤ} (h0 : γ ⟨0, by omega⟩ = 0)
    (h1 : γ ⟨1, by omega⟩ = 0) (x : F) :
    oaPsiL Θ φ₀ φ₁ γ x = Θ (minusXL (m + 4) b c (shiftB γ) x) := by
  have hne0 : ∀ v : Fin (m + 4 + 2 - 1) → ℤ, v ⟨0, by omega⟩ ≠ 0 → γ ≠ v := fun v hv h =>
    hv (by rw [← h]; exact h0)
  have hne1 : ∀ v : Fin (m + 4 + 2 - 1) → ℤ, v ⟨1, by omega⟩ ≠ 0 → γ ≠ v := fun v hv h =>
    hv (by rw [← h]; exact h1)
  rw [oaPsiL, ite_eq_right (hne0 _ (by simp)), ite_eq_right (hne0 _ (by simp)),
    ite_eq_right (hne1 _ (by simp)), ite_eq_right (hne1 _ (by simp)),
    ite_eq_right (hne0 _ (by simp)), ite_eq_right (hne0 _ (by simp)),
    ite_eq_right (hne1 _ (by simp)), ite_eq_right (hne1 _ (by simp))]

theorem oaPsiL_add (γ : Fin (m + 4 + 2 - 1) → ℤ) (x y : F) :
    oaPsiL Θ φ₀ φ₁ γ (x + y) = oaPsiL Θ φ₀ φ₁ γ x * oaPsiL Θ φ₀ φ₁ γ y := by
  unfold oaPsiL
  split_ifs <;> first | rw [tv_add, map_mul] | rw [minusXL_add, map_mul]

theorem oaPsiS_add (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (γ : Fin (m + 4 + 2 - 1) → ℤ)
    (p q : Fin 2 → F) :
    oaPsiS hirr Θ γ (p + q) = oaPsiS hirr Θ γ p * oaPsiS hirr Θ γ q := by
  rw [oaPsiS, oaPsiS, oaPsiS, minusXS_add, map_mul]

theorem oaPsiL_up (k : Fin (m + 4 - 1)) (x : F) :
    oaPsiL Θ φ₀ φ₁ (Pi.single (upB k) 1) x = Θ (minusXL (m + 4) b c (Pi.single k 1) x) := by
  rw [oaPsiL_of_last Θ φ₀ φ₁ (single_upB_zero k) (single_upB_one k), shiftB_single_upB]

theorem oaPsiL_neg_up (k : Fin (m + 4 - 1)) (x : F) :
    oaPsiL Θ φ₀ φ₁ (-Pi.single (upB k) 1) x = Θ (minusXL (m + 4) b c (-Pi.single k 1) x) := by
  rw [oaPsiL_of_last Θ φ₀ φ₁ (by simp) (by simp), shiftB_neg, shiftB_single_upB]

theorem oaPsiL_up_add (k k' : Fin (m + 4 - 1)) (x : F) :
    oaPsiL Θ φ₀ φ₁ (Pi.single (upB k) 1 + Pi.single (upB k') 1) x =
      Θ (minusXL (m + 4) b c (Pi.single k 1 + Pi.single k' 1) x) := by
  rw [oaPsiL_of_last Θ φ₀ φ₁ (by simp) (by simp), shiftB_add, shiftB_single_upB,
    shiftB_single_upB]

theorem oaPsiL_up_add_two (k k' : Fin (m + 4 - 1)) (x : F) :
    oaPsiL Θ φ₀ φ₁ (Pi.single (upB k) 1 + 2 • Pi.single (upB k') 1) x =
      Θ (minusXL (m + 4) b c (Pi.single k 1 + 2 • Pi.single k' 1) x) := by
  rw [oaPsiL_of_last Θ φ₀ φ₁ (by simp) (by simp), shiftB_add, shiftB_smul, shiftB_single_upB,
    shiftB_single_upB]

theorem oaPsiS_up (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k : Fin (m + 4 - 1)) (p : Fin 2 → F) :
    oaPsiS hirr Θ (Pi.single (upB k) 1) p = Θ (minusXS (m + 4) hirr (Pi.single k 1) p) := by
  rw [oaPsiS, shiftB_single_upB]

theorem oaPsiS_neg_up (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k : Fin (m + 4 - 1))
    (p : Fin 2 → F) :
    oaPsiS hirr Θ (-Pi.single (upB k) 1) p = Θ (minusXS (m + 4) hirr (-Pi.single k 1) p) := by
  rw [oaPsiS, shiftB_neg, shiftB_single_upB]

theorem oaPsiS_up_add (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k k' : Fin (m + 4 - 1))
    (p : Fin 2 → F) :
    oaPsiS hirr Θ (Pi.single (upB k) 1 + Pi.single (upB k') 1) p =
      Θ (minusXS (m + 4) hirr (Pi.single k 1 + Pi.single k' 1) p) := by
  rw [oaPsiS, shiftB_add, shiftB_single_upB, shiftB_single_upB]

end FrameM

section PairsM

variable {m : ℕ}

theorem minusM_neg_mem {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅) :
    -γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅ :=
  (Steinberg.RootSystem.ofCartan (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅).neg_mem _ hγ

theorem minusM_pos_or_neg {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅) :
    0 < Steinberg.ht γ ∨ 0 < Steinberg.ht (-γ) := by
  have hne := RootSystem.ne_zero_of_mem_roots _ _ hγ
  rcases RootSystem.nonneg_or_nonpos _ _ hγ with h | h
  · exact Or.inl (lt_of_lt_of_le one_pos (RootSystem.one_le_sum_of_nonneg h hne))
  · exact Or.inr (lt_of_lt_of_le one_pos
      (RootSystem.one_le_sum_of_nonneg (neg_nonneg.2 h) (neg_ne_zero.2 hne)))

theorem minusM_pair01 {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ ⟨1, by omega⟩ → γ l = 0) :
    γ = d0 m ∨ γ = -d0 m ∨ γ = d1 m ∨ γ = -d1 m ∨ γ = d0 m + d1 m ∨ γ = -(d0 m + d1 m) := by
  have hs' : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ ⟨1, by omega⟩ → (-γ) l = 0 := fun l h1 h2 => by
    rw [Pi.neg_apply, hs l h1 h2, neg_zero]
  rcases minusM_pos_or_neg hγ with hp | hp
  · rcases minus_pos_roots_A2 (n := m + 4 + 2) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp only; omega) rfl hγ hs hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases minus_pos_roots_A2 (n := m + 4 + 2) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
      (by simp only; omega) rfl (minusM_neg_mem hγ) hs' hp with h | h | h
    · exact Or.inr (Or.inl (neg_eq_iff_eq_neg.1 h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (neg_eq_iff_eq_neg.1 h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (neg_eq_iff_eq_neg.1 h))))

theorem minusM_pair12 {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ ⟨2, by omega⟩ → γ l = 0) :
    γ = d1 m ∨ γ = -d1 m ∨ γ = d2 m ∨ γ = -d2 m ∨ γ = d1 m + d2 m ∨ γ = -(d1 m + d2 m) := by
  have hs' : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ ⟨2, by omega⟩ → (-γ) l = 0 := fun l h1 h2 => by
    rw [Pi.neg_apply, hs l h1 h2, neg_zero]
  rcases minusM_pos_or_neg hγ with hp | hp
  · rcases minus_pos_roots_A2 (n := m + 4 + 2) (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩)
      (by simp only; omega) rfl hγ hs hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases minus_pos_roots_A2 (n := m + 4 + 2) (i := ⟨1, by omega⟩) (j := ⟨2, by omega⟩)
      (by simp only; omega) rfl (minusM_neg_mem hγ) hs' hp with h | h | h
    · exact Or.inr (Or.inl (neg_eq_iff_eq_neg.1 h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (neg_eq_iff_eq_neg.1 h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (neg_eq_iff_eq_neg.1 h))))

theorem minusM_pairA1 {i : Fin (m + 4 + 2 - 1)} {j : Fin (m + 4 - 1)} (hij : i.val + 2 ≤ j.val + 2)
    {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ i → l ≠ upB j → γ l = 0) :
    γ = Pi.single i 1 ∨ γ = -Pi.single i 1 ∨ γ = Pi.single (upB j) 1 ∨
      γ = -Pi.single (upB j) 1 := by
  have hs' : ∀ l, l ≠ i → l ≠ upB j → (-γ) l = 0 := fun l h1 h2 => by
    rw [Pi.neg_apply, hs l h1 h2, neg_zero]
  rcases minusM_pos_or_neg hγ with hp | hp
  · rcases minus_pos_roots_A1A1 (n := m + 4 + 2) (i := i) (j := upB j) hij hγ hs hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases minus_pos_roots_A1A1 (n := m + 4 + 2) (i := i) (j := upB j) hij (minusM_neg_mem hγ)
      hs' hp with h | h
    · exact Or.inr (Or.inl (neg_eq_iff_eq_neg.1 h))
    · exact Or.inr (Or.inr (Or.inr (neg_eq_iff_eq_neg.1 h)))

end PairsM

section BGen

variable {N : ℕ}

theorem cartanB_self (i : Fin N) : cartanB N i i = 2 := by
  simp [cartanB]

theorem cartanB_far {i j : Fin N} (h : i.val + 2 ≤ j.val) :
    cartanB N i j = 0 ∧ cartanB N j i = 0 := by
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  constructor <;> split_ifs <;> omega

theorem cartanB_succ {i j : Fin N} (hij : i.val + 1 = j.val) (h : j.val + 1 < N) :
    cartanB N i j = -1 ∧ cartanB N j i = -1 := by
  simp only [cartanB, Matrix.of_apply, Fin.ext_iff]
  constructor <;> split_ifs <;> omega

theorem reflectionB_far {i j : Fin N} (h : cartanB N i j = 0) :
    reflection (cartanB N) i (Pi.single j 1) = Pi.single j 1 := by
  rw [reflection_single', h, zero_smul, sub_zero]

theorem reflectionB_A2 {p q : Fin N} (hpq : p.val + 1 = q.val) (hq : q.val + 1 < N) :
    reflection (cartanB N) p (Pi.single p 1) = -Pi.single p 1 ∧
    reflection (cartanB N) p (Pi.single q 1) = Pi.single p 1 + Pi.single q 1 ∧
    reflection (cartanB N) p (Pi.single p 1 + Pi.single q 1) = Pi.single q 1 ∧
    reflection (cartanB N) q (Pi.single p 1) = Pi.single p 1 + Pi.single q 1 ∧
    reflection (cartanB N) q (Pi.single q 1) = -Pi.single q 1 ∧
    reflection (cartanB N) q (Pi.single p 1 + Pi.single q 1) = Pi.single p 1 := by
  obtain ⟨h1, h2⟩ := cartanB_succ hpq hq
  have rpp : reflection (cartanB N) p (Pi.single p 1) = -Pi.single p 1 :=
    reflection_single_self (cartanB_self p)
  have rqq : reflection (cartanB N) q (Pi.single q 1) = -Pi.single q 1 :=
    reflection_single_self (cartanB_self q)
  have rpq : reflection (cartanB N) p (Pi.single q 1) = Pi.single p 1 + Pi.single q 1 := by
    rw [reflection_single', h1]
    module
  have rqp : reflection (cartanB N) q (Pi.single p 1) = Pi.single p 1 + Pi.single q 1 := by
    rw [reflection_single', h2]
    module
  refine ⟨rpp, rpq, ?_, rqp, rqq, ?_⟩
  · rw [map_add, rpp, rpq]
    abel
  · rw [map_add, rqp, rqq]
    abel

end BGen

theorem minusWeyl_eq_long {n : ℕ} {F : Type} [Field F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k : Fin (n - 1)} (hk : k.val + 2 < n) :
    minusWeyl n hirr k = minusXL n b c (Pi.single k 1) 1 * minusXL n b c (-Pi.single k 1) (-1) *
      minusXL n b c (Pi.single k 1) 1 := by
  have hk' : k.val + 1 < n - 1 := by omega
  rw [minusWeyl_of_lt n hirr hk', HypFrame.longWeyl_eq, minusXL_single hk,
    minusXL_eq (succ_ne_of_lt n hk').symm true false (toStdB_neg_single_of_lt' n hk'),
    mlr_of_ne (succ_ne_of_lt n hk'), mlr_of_ne (succ_ne_of_lt n hk').symm]
  rfl

section FrameThmM

variable {G : Type} [Group G] {m : ℕ} {F : Type} [Field F] {b c : F}

abbrev y0 (m : ℕ) : Fin (m + 4 - 1) := ⟨0, by omega⟩

structure FrameHypM (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Θ : spinGroup (quadMinus (m + 4) F b c) →* G) (φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G)
    (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G) : Prop where
  φ₀01 : ∀ x, φ₀ (tv 0 1 x) = ρ₀ (tv 0 1 x)
  φ₀10 : ∀ x, φ₀ (tv 1 0 x) = ρ₀ (tv 1 0 x)
  φ₀12 : ∀ x, φ₀ (tv 1 2 x) = ρ₁ (tv 0 1 x)
  φ₀21 : ∀ x, φ₀ (tv 2 1 x) = ρ₁ (tv 1 0 x)
  φ₁01 : ∀ x, φ₁ (tv 0 1 x) = ρ₁ (tv 0 1 x)
  φ₁10 : ∀ x, φ₁ (tv 1 0 x) = ρ₁ (tv 1 0 x)
  φ₁12 : ∀ x, φ₁ (tv 1 2 x) = Θ (minusXL (m + 4) b c (Pi.single (y0 m) 1) x)
  φ₁21 : ∀ x, φ₁ (tv 2 1 x) = Θ (minusXL (m + 4) b c (-Pi.single (y0 m) 1) x)
  V : ∀ g y, Commute (ρ₀ g) (Θ y)
  E : ∀ k : Fin (m + 4 - 1), k.val ≠ 0 → ∀ g,
    ∀ y ∈ (minusDatum (m + 4) hirr).rootGroup (Pi.single k 1) ⊔
      (minusDatum (m + 4) hirr).rootGroup (-Pi.single k 1), Commute (ρ₁ g) (Θ y)

variable [CharP F 2]

@[expose] noncomputable def oaNM (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (Θ : spinGroup (quadMinus (m + 4) F b c) →* G) (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G)
    (k : Fin (m + 4 + 2 - 1)) : G :=
  if k.val = 0 then ρ₀ (pmat (Equiv.swap 0 1)) else if k.val = 1 then ρ₁ (pmat (Equiv.swap 0 1))
  else Θ (minusWeyl (m + 4) hirr ⟨k.val - 2, by omega⟩)

variable (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (Θ : spinGroup (quadMinus (m + 4) F b c) →* G)
  (φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G) (ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G)

theorem oaNM_zero : oaNM hirr Θ ρ₀ ρ₁ ⟨0, by omega⟩ = ρ₀ (pmat (Equiv.swap 0 1)) := by
  rw [oaNM, ite_eq_left rfl]

theorem oaNM_one : oaNM hirr Θ ρ₀ ρ₁ ⟨1, by omega⟩ = ρ₁ (pmat (Equiv.swap 0 1)) := by
  rw [oaNM, ite_eq_right (show ¬ (1 = 0) by omega), ite_eq_left rfl]

theorem oaNM_up (k : Fin (m + 4 - 1)) :
    oaNM hirr Θ ρ₀ ρ₁ (upB k) = Θ (minusWeyl (m + 4) hirr k) := by
  rw [oaNM, ite_eq_right (show ¬ (k.val + 2 = 0) by omega),
    ite_eq_right (show ¬ (k.val + 2 = 1) by omega)]
  rfl

theorem oaNM_conj_lastL {γ : Fin (m + 4 + 2 - 1) → ℤ} (hγ : MinusLong (m + 4 + 2) γ)
    (h0 : γ ⟨0, by omega⟩ = 0) (h1 : γ ⟨1, by omega⟩ = 0) (k : Fin (m + 4 - 1)) (x : F) :
    oaNM hirr Θ ρ₀ ρ₁ (upB k) * oaPsiL Θ φ₀ φ₁ γ x * (oaNM hirr Θ ρ₀ ρ₁ (upB k))⁻¹ =
      oaPsiL Θ φ₀ φ₁ (reflection (cartanB (m + 4 + 2 - 1)) (upB k) γ) x := by
  rw [oaNM_up, oaPsiL_of_last Θ φ₀ φ₁ h0 h1,
    oaPsiL_of_last Θ φ₀ φ₁ (reflectionB_apply_zero k h0) (reflectionB_apply_one k h1),
    shiftB_reflection k h0 h1, ← map_inv, ← map_mul, ← map_mul,
    minusWeyl_conj_minusXL hirr k (minusLong_shiftB (by omega) hγ h0 h1)]

theorem oaNM_conj_lastS {γ : Fin (m + 4 + 2 - 1) → ℤ} (hγ : MinusShort (m + 4 + 2) γ)
    (h0 : γ ⟨0, by omega⟩ = 0) (h1 : γ ⟨1, by omega⟩ = 0) (k : Fin (m + 4 - 1))
    (p : Fin 2 → F) :
    oaNM hirr Θ ρ₀ ρ₁ (upB k) * oaPsiS hirr Θ γ p * (oaNM hirr Θ ρ₀ ρ₁ (upB k))⁻¹ =
      oaPsiS hirr Θ (reflection (cartanB (m + 4 + 2 - 1)) (upB k) γ)
        (if (upB k).val + 2 = m + 4 + 2 then planeRefl b c planeOne p else p) := by
  rw [oaNM_up, oaPsiS, oaPsiS, shiftB_reflection k h0 h1, ← map_inv, ← map_mul, ← map_mul,
    minusWeyl_conj_minusXS hirr k (minusShort_shiftB (by omega) hγ h0 h1)]
  have e : (upB k).val = k.val + 2 := rfl
  by_cases hk : k.val + 2 = m + 4
  · rw [ite_eq_left hk, ite_eq_left (by rw [e]; omega)]
  · rw [ite_eq_right hk, ite_eq_right (by rw [e]; omega)]

variable {hirr Θ φ₀ φ₁ ρ₀ ρ₁} (H : FrameHypM hirr Θ φ₀ φ₁ ρ₀ ρ₁)
include H

omit [CharP F 2] in
theorem FrameHypM.v_d0 (x : F) : oaPsiL Θ φ₀ φ₁ (d0 m) x = ρ₀ (tv 0 1 x) :=
  (oaPsiL_d0 Θ φ₀ φ₁ x).trans (H.φ₀01 x)

omit [CharP F 2] in
theorem FrameHypM.v_nd0 (x : F) : oaPsiL Θ φ₀ φ₁ (-d0 m) x = ρ₀ (tv 1 0 x) :=
  (oaPsiL_nd0 Θ φ₀ φ₁ x).trans (H.φ₀10 x)

omit [CharP F 2] in
theorem FrameHypM.v_d1 (x : F) : oaPsiL Θ φ₀ φ₁ (d1 m) x = ρ₁ (tv 0 1 x) :=
  (oaPsiL_d1 Θ φ₀ φ₁ x).trans (H.φ₀12 x)

omit [CharP F 2] in
theorem FrameHypM.v_nd1 (x : F) : oaPsiL Θ φ₀ φ₁ (-d1 m) x = ρ₁ (tv 1 0 x) :=
  (oaPsiL_nd1 Θ φ₀ φ₁ x).trans (H.φ₀21 x)

omit [CharP F 2] in
theorem FrameHypM.w_d1 (x : F) : oaPsiL Θ φ₀ φ₁ (d1 m) x = φ₁ (tv 0 1 x) :=
  (H.v_d1 x).trans (H.φ₁01 x).symm

omit [CharP F 2] in
theorem FrameHypM.w_nd1 (x : F) : oaPsiL Θ φ₀ φ₁ (-d1 m) x = φ₁ (tv 1 0 x) :=
  (H.v_nd1 x).trans (H.φ₁10 x).symm

omit [CharP F 2] in
theorem FrameHypM.w_d2 (x : F) : oaPsiL Θ φ₀ φ₁ (d2 m) x = φ₁ (tv 1 2 x) :=
  (oaPsiL_up Θ φ₀ φ₁ (y0 m) x).trans (H.φ₁12 x).symm

omit [CharP F 2] in
theorem FrameHypM.w_nd2 (x : F) : oaPsiL Θ φ₀ φ₁ (-d2 m) x = φ₁ (tv 2 1 x) :=
  (oaPsiL_neg_up Θ φ₀ φ₁ (y0 m) x).trans (H.φ₁21 x).symm

theorem FrameHypM.oaNM_zero_eq :
    oaNM hirr Θ ρ₀ ρ₁ ⟨0, by omega⟩ = φ₀ (pmat (Equiv.swap 0 1)) := by
  rw [oaNM_zero, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (0 : Fin 3) ≠ 1 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₀01,
    H.φ₀10]

theorem FrameHypM.oaNM_one_eq₀ :
    oaNM hirr Θ ρ₀ ρ₁ ⟨1, by omega⟩ = φ₀ (pmat (Equiv.swap 1 2)) := by
  rw [oaNM_one, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (1 : Fin 3) ≠ 2 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₀12,
    H.φ₀21]

theorem FrameHypM.oaNM_one_eq₁ :
    oaNM hirr Θ ρ₀ ρ₁ ⟨1, by omega⟩ = φ₁ (pmat (Equiv.swap 0 1)) := by
  rw [oaNM_one, pmat_swap (show (0 : Fin 2) ≠ 1 by decide),
    pmat_swap (show (0 : Fin 3) ≠ 1 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₁01,
    H.φ₁10]

theorem FrameHypM.oaNM_two_eq :
    oaNM hirr Θ ρ₀ ρ₁ (upB (y0 m)) = φ₁ (pmat (Equiv.swap 1 2)) := by
  rw [oaNM_up, minusWeyl_eq_long hirr (show (y0 m).val + 2 < m + 4 by simp),
    pmat_swap (show (1 : Fin 3) ≠ 2 by decide), map_mul, map_mul, map_mul, map_mul, H.φ₁12,
    H.φ₁21, CharTwo.neg_eq (R := F)]

theorem FrameHypM.commute_oaNM_up_ρ₀ (k : Fin (m + 4 - 1)) (g : SpecialLinearGroup (Fin 2) F) :
    Commute (oaNM hirr Θ ρ₀ ρ₁ (upB k)) (ρ₀ g) := by
  rw [oaNM_up]
  exact (H.V g _).symm

theorem FrameHypM.commute_oaNM_up_ρ₁ (k : Fin (m + 4 - 1)) (hk : k.val ≠ 0)
    (g : SpecialLinearGroup (Fin 2) F) : Commute (oaNM hirr Θ ρ₀ ρ₁ (upB k)) (ρ₁ g) := by
  rw [oaNM_up]
  exact (H.E k hk g _ (minusDatum_n_mem (m + 4) hirr k)).symm

omit [CharP F 2] in
theorem FrameHypM.commute_long (k : Fin (m + 4 - 1)) (hk : k.val ≠ 0) (hk' : k.val + 2 < m + 4)
    (g : SpecialLinearGroup (Fin 2) F) (x : F) :
    Commute (ρ₁ g) (Θ (minusXL (m + 4) b c (Pi.single k 1) x)) ∧
      Commute (ρ₁ g) (Θ (minusXL (m + 4) b c (-Pi.single k 1) x)) :=
  ⟨H.E k hk g _ (Subgroup.mem_sup_left (minusXL_mem hirr (minusLong_single hk') x)),
    H.E k hk g _ (Subgroup.mem_sup_right (minusXL_mem hirr (minusLong_neg_single hk') x))⟩

omit [CharP F 2] in
theorem FrameHypM.commute_short (k : Fin (m + 4 - 1)) (hk : k.val ≠ 0) (hk' : k.val + 2 = m + 4)
    (g : SpecialLinearGroup (Fin 2) F) (p : Fin 2 → F) :
    Commute (ρ₁ g) (Θ (minusXS (m + 4) hirr (Pi.single k 1) p)) ∧
      Commute (ρ₁ g) (Θ (minusXS (m + 4) hirr (-Pi.single k 1) p)) :=
  ⟨H.E k hk g _ (Subgroup.mem_sup_left (minusXS_mem hirr (minusShort_single hk') p)),
    H.E k hk g _ (Subgroup.mem_sup_right (minusXS_mem hirr (minusShort_neg_single hk') p))⟩

end FrameThmM

section FrameWeylM

variable {G : Type} [Group G] {m : ℕ} {F : Type} [Field F] [CharP F 2] {b c : F}
  {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {Θ : spinGroup (quadMinus (m + 4) F b c) →* G}
  {φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G} {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G}
  (H : FrameHypM hirr Θ φ₀ φ₁ ρ₀ ρ₁)

omit [Field F] [CharP F 2] in
theorem minusLong_pair01 {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ ⟨1, by omega⟩ → γ l = 0) : MinusLong (m + 4 + 2) γ := by
  rcases minusM_pair01 hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact minusLong_single (show 0 + 2 < m + 4 + 2 by omega)
  · exact minusLong_neg_single (show 0 + 2 < m + 4 + 2 by omega)
  · exact minusLong_single (show 1 + 2 < m + 4 + 2 by omega)
  · exact minusLong_neg_single (show 1 + 2 < m + 4 + 2 by omega)
  · exact minusLong_A2sum (i := ⟨0, by omega⟩) (show 0 + 3 < m + 4 + 2 by omega)
  · exact minusLong_neg' (minusLong_A2sum (i := ⟨0, by omega⟩) (show 0 + 3 < m + 4 + 2 by omega))

omit [Field F] [CharP F 2] in
theorem minusLong_pair12 {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ ⟨2, by omega⟩ → γ l = 0) : MinusLong (m + 4 + 2) γ := by
  rcases minusM_pair12 hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact minusLong_single (show 1 + 2 < m + 4 + 2 by omega)
  · exact minusLong_neg_single (show 1 + 2 < m + 4 + 2 by omega)
  · exact minusLong_single (show 2 + 2 < m + 4 + 2 by omega)
  · exact minusLong_neg_single (show 2 + 2 < m + 4 + 2 by omega)
  · exact minusLong_A2sum (i := ⟨1, by omega⟩) (show 1 + 3 < m + 4 + 2 by omega)
  · exact minusLong_neg' (minusLong_A2sum (i := ⟨1, by omega⟩) (show 1 + 3 < m + 4 + 2 by omega))

include H

theorem FrameHypM.weyl01 {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ ⟨1, by omega⟩ → γ l = 0) {k : Fin (m + 4 + 2 - 1)}
    (hk : k = ⟨0, by omega⟩ ∨ k = ⟨1, by omega⟩) (x : F) :
    oaNM hirr Θ ρ₀ ρ₁ k * oaPsiL Θ φ₀ φ₁ γ x * (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ =
      oaPsiL Θ φ₀ φ₁ (reflection (cartanB (m + 4 + 2 - 1)) k γ) x := by
  obtain ⟨r00, r01, r0s, r10, r11, r1s⟩ := reflectionB_A2 (N := m + 4 + 2 - 1)
    (p := ⟨0, by omega⟩) (q := ⟨1, by omega⟩) rfl (by simp only; omega)
  rcases hk with rfl | rfl
  · rw [H.oaNM_zero_eq]
    rcases minusM_pair01 hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r00, oaPsiL_d0, oaPsiL_nd0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r00, neg_neg, oaPsiL_nd0, oaPsiL_d0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r01, oaPsiL_d1, oaPsiL_d01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r01, oaPsiL_nd1, oaPsiL_nd01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r0s, oaPsiL_d01, oaPsiL_d1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r0s, oaPsiL_nd01, oaPsiL_nd1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
  · rw [H.oaNM_one_eq₀]
    rcases minusM_pair01 hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r10, oaPsiL_d0, oaPsiL_d01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r10, oaPsiL_nd0, oaPsiL_nd01]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r11, oaPsiL_d1, oaPsiL_nd1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r11, neg_neg, oaPsiL_nd1, oaPsiL_d1]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [r1s, oaPsiL_d01, oaPsiL_d0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r1s, oaPsiL_nd01, oaPsiL_nd0]
      exact conj_pmat φ₀ _ (by decide) (by decide) (by decide) x

theorem FrameHypM.weyl12 {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ ⟨2, by omega⟩ → γ l = 0) {k : Fin (m + 4 + 2 - 1)}
    (hk : k = ⟨1, by omega⟩ ∨ k = upB (y0 m)) (x : F) :
    oaNM hirr Θ ρ₀ ρ₁ k * oaPsiL Θ φ₀ φ₁ γ x * (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ =
      oaPsiL Θ φ₀ φ₁ (reflection (cartanB (m + 4 + 2 - 1)) k γ) x := by
  obtain ⟨r11, r12, r1s, r21, r22, r2s⟩ := reflectionB_A2 (N := m + 4 + 2 - 1)
    (p := ⟨1, by omega⟩) (q := upB (y0 m)) rfl (by simp only; omega)
  rcases hk with rfl | rfl
  · rw [H.oaNM_one_eq₁]
    rcases minusM_pair12 hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r11, H.w_d1, H.w_nd1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r11, neg_neg, H.w_nd1, H.w_d1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r12, H.w_d2, oaPsiL_d12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r12, H.w_nd2, oaPsiL_nd12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r1s, oaPsiL_d12, H.w_d2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r1s, oaPsiL_nd12, H.w_nd2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
  · rw [H.oaNM_two_eq]
    rcases minusM_pair12 hγ hs with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [r21, H.w_d1, oaPsiL_d12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r21, H.w_nd1, oaPsiL_nd12]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r22, H.w_d2, H.w_nd2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r22, neg_neg, H.w_nd2, H.w_d2]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [r2s, oaPsiL_d12, H.w_d1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, r2s, oaPsiL_nd12, H.w_nd1]
      exact conj_pmat φ₁ _ (by decide) (by decide) (by decide) x

theorem FrameHypM.weyl0j (j : Fin (m + 4 - 1)) {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨0, by omega⟩ → l ≠ upB j → γ l = 0) {k : Fin (m + 4 + 2 - 1)}
    (hk : k = ⟨0, by omega⟩ ∨ k = upB j) :
    (MinusLong (m + 4 + 2) γ → ∀ x, oaNM hirr Θ ρ₀ ρ₁ k * oaPsiL Θ φ₀ φ₁ γ x *
      (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ = oaPsiL Θ φ₀ φ₁ (reflection (cartanB (m + 4 + 2 - 1)) k γ) x) ∧
    (MinusShort (m + 4 + 2) γ → ∀ p, oaNM hirr Θ ρ₀ ρ₁ k * oaPsiS hirr Θ γ p *
      (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ = oaPsiS hirr Θ (reflection (cartanB (m + 4 + 2 - 1)) k γ)
        (if k.val + 2 = m + 4 + 2 then planeRefl b c planeOne p else p)) := by
  obtain ⟨h0j, hj0⟩ := cartanB_far (N := m + 4 + 2 - 1) (i := ⟨0, by omega⟩) (j := upB j)
    (show 0 + 2 ≤ j.val + 2 by omega)
  have r00 : reflection (cartanB (m + 4 + 2 - 1)) ⟨0, by omega⟩ (d0 m) = -d0 m :=
    reflection_single_self (cartanB_self _)
  have hd0 : MinusLong (m + 4 + 2) (d0 m) := minusLong_single (show 0 + 2 < m + 4 + 2 by omega)
  rcases minusM_pairA1 (i := ⟨0, by omega⟩) (j := j) (show 0 + 2 ≤ j.val + 2 by omega) hγ hs with
    rfl | rfl | rfl | rfl
  · refine ⟨fun _ x => ?_, fun hS => absurd hd0 hS.not_long⟩
    rcases hk with rfl | rfl
    · rw [r00, H.v_d0, H.v_nd0, oaNM_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) x
    · rw [reflectionB_far hj0, H.v_d0]
      exact conj_of_commute' (H.commute_oaNM_up_ρ₀ j _)
  · refine ⟨fun _ x => ?_, fun hS => absurd (minusLong_neg' hd0) hS.not_long⟩
    rcases hk with rfl | rfl
    · rw [map_neg, r00, neg_neg, H.v_nd0, H.v_d0, oaNM_zero]
      exact conj_pmat ρ₀ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, reflectionB_far hj0, H.v_nd0]
      exact conj_of_commute' (H.commute_oaNM_up_ρ₀ j _)
  · refine ⟨fun hL x => ?_, fun hS p => ?_⟩
    · rcases hk with rfl | rfl
      · rw [reflectionB_far h0j, oaNM_zero, oaPsiL_up]
        exact conj_of_commute' (H.V _ _)
      · exact oaNM_conj_lastL hirr Θ φ₀ φ₁ ρ₀ ρ₁ hL (single_upB_zero j) (single_upB_one j) j x
    · rcases hk with rfl | rfl
      · rw [reflectionB_far h0j, oaNM_zero, ite_eq_right (show ¬ (0 + 2 = m + 4 + 2) by omega),
          oaPsiS_up]
        exact conj_of_commute' (H.V _ _)
      · exact oaNM_conj_lastS hirr Θ ρ₀ ρ₁ hS (single_upB_zero j) (single_upB_one j) j p
  · refine ⟨fun hL x => ?_, fun hS p => ?_⟩
    · rcases hk with rfl | rfl
      · rw [map_neg, reflectionB_far h0j, oaNM_zero, oaPsiL_neg_up]
        exact conj_of_commute' (H.V _ _)
      · exact oaNM_conj_lastL hirr Θ φ₀ φ₁ ρ₀ ρ₁ hL (by simp) (by simp) j x
    · rcases hk with rfl | rfl
      · rw [map_neg, reflectionB_far h0j, oaNM_zero,
          ite_eq_right (show ¬ (0 + 2 = m + 4 + 2) by omega), oaPsiS_neg_up]
        exact conj_of_commute' (H.V _ _)
      · exact oaNM_conj_lastS hirr Θ ρ₀ ρ₁ hS (by simp) (by simp) j p

theorem FrameHypM.weyl1j (j : Fin (m + 4 - 1)) (hj : j.val ≠ 0) {γ : Fin (m + 4 + 2 - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅)
    (hs : ∀ l, l ≠ ⟨1, by omega⟩ → l ≠ upB j → γ l = 0) {k : Fin (m + 4 + 2 - 1)}
    (hk : k = ⟨1, by omega⟩ ∨ k = upB j) :
    (MinusLong (m + 4 + 2) γ → ∀ x, oaNM hirr Θ ρ₀ ρ₁ k * oaPsiL Θ φ₀ φ₁ γ x *
      (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ = oaPsiL Θ φ₀ φ₁ (reflection (cartanB (m + 4 + 2 - 1)) k γ) x) ∧
    (MinusShort (m + 4 + 2) γ → ∀ p, oaNM hirr Θ ρ₀ ρ₁ k * oaPsiS hirr Θ γ p *
      (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ = oaPsiS hirr Θ (reflection (cartanB (m + 4 + 2 - 1)) k γ)
        (if k.val + 2 = m + 4 + 2 then planeRefl b c planeOne p else p)) := by
  obtain ⟨h1j, hj1⟩ := cartanB_far (N := m + 4 + 2 - 1) (i := ⟨1, by omega⟩) (j := upB j)
    (show 1 + 2 ≤ j.val + 2 by omega)
  have r11 : reflection (cartanB (m + 4 + 2 - 1)) ⟨1, by omega⟩ (d1 m) = -d1 m :=
    reflection_single_self (cartanB_self _)
  have hd1 : MinusLong (m + 4 + 2) (d1 m) := minusLong_single (show 1 + 2 < m + 4 + 2 by omega)
  have hJL : MinusLong (m + 4 + 2) (Pi.single (upB j) 1) → MinusLong (m + 4) (Pi.single j 1) :=
    fun hL => by
      have := minusLong_shiftB (by omega) hL (single_upB_zero j) (single_upB_one j)
      rwa [shiftB_single_upB] at this
  have hJS : MinusShort (m + 4 + 2) (Pi.single (upB j) 1) →
      MinusShort (m + 4) (Pi.single j 1) := fun hS => by
    have := minusShort_shiftB (by omega) hS (single_upB_zero j) (single_upB_one j)
    rwa [shiftB_single_upB] at this
  have hJL' : MinusLong (m + 4 + 2) (-Pi.single (upB j) 1) →
      MinusLong (m + 4) (-Pi.single j 1) := fun hL => by
    have := minusLong_shiftB (by omega) hL (by simp) (by simp)
    rwa [shiftB_neg, shiftB_single_upB] at this
  have hJS' : MinusShort (m + 4 + 2) (-Pi.single (upB j) 1) →
      MinusShort (m + 4) (-Pi.single j 1) := fun hS => by
    have := minusShort_shiftB (by omega) hS (by simp) (by simp)
    rwa [shiftB_neg, shiftB_single_upB] at this
  have hsup : ∀ y, (y ∈ (minusDatum (m + 4) hirr).rootGroup (Pi.single j 1) ∨
      y ∈ (minusDatum (m + 4) hirr).rootGroup (-Pi.single j 1)) → ∀ g,
      Commute (ρ₁ g) (Θ y) := fun y hy g =>
    H.E j hj g y (hy.elim (fun h => Subgroup.mem_sup_left h) (fun h => Subgroup.mem_sup_right h))
  rcases minusM_pairA1 (i := ⟨1, by omega⟩) (j := j) (show 1 + 2 ≤ j.val + 2 by omega) hγ hs with
    rfl | rfl | rfl | rfl
  · refine ⟨fun _ x => ?_, fun hS => absurd hd1 hS.not_long⟩
    rcases hk with rfl | rfl
    · rw [r11, H.v_d1, H.v_nd1, oaNM_one]
      exact conj_pmat ρ₁ _ (by decide) (by decide) (by decide) x
    · rw [reflectionB_far hj1, H.v_d1]
      exact conj_of_commute' (H.commute_oaNM_up_ρ₁ j hj _)
  · refine ⟨fun _ x => ?_, fun hS => absurd (minusLong_neg' hd1) hS.not_long⟩
    rcases hk with rfl | rfl
    · rw [map_neg, r11, neg_neg, H.v_nd1, H.v_d1, oaNM_one]
      exact conj_pmat ρ₁ _ (by decide) (by decide) (by decide) x
    · rw [map_neg, reflectionB_far hj1, H.v_nd1]
      exact conj_of_commute' (H.commute_oaNM_up_ρ₁ j hj _)
  · refine ⟨fun hL x => ?_, fun hS p => ?_⟩
    · rcases hk with rfl | rfl
      · rw [reflectionB_far h1j, oaNM_one, oaPsiL_up]
        exact conj_of_commute' (hsup _ (Or.inl (minusXL_mem hirr (hJL hL) x)) _)
      · exact oaNM_conj_lastL hirr Θ φ₀ φ₁ ρ₀ ρ₁ hL (single_upB_zero j) (single_upB_one j) j x
    · rcases hk with rfl | rfl
      · rw [reflectionB_far h1j, oaNM_one, ite_eq_right (show ¬ (1 + 2 = m + 4 + 2) by omega),
          oaPsiS_up]
        exact conj_of_commute' (hsup _ (Or.inl (minusXS_mem hirr (hJS hS) p)) _)
      · exact oaNM_conj_lastS hirr Θ ρ₀ ρ₁ hS (single_upB_zero j) (single_upB_one j) j p
  · refine ⟨fun hL x => ?_, fun hS p => ?_⟩
    · rcases hk with rfl | rfl
      · rw [map_neg, reflectionB_far h1j, oaNM_one, oaPsiL_neg_up]
        exact conj_of_commute' (hsup _ (Or.inr (minusXL_mem hirr (hJL' hL) x)) _)
      · exact oaNM_conj_lastL hirr Θ φ₀ φ₁ ρ₀ ρ₁ hL (by simp) (by simp) j x
    · rcases hk with rfl | rfl
      · rw [map_neg, reflectionB_far h1j, oaNM_one,
          ite_eq_right (show ¬ (1 + 2 = m + 4 + 2) by omega), oaPsiS_neg_up]
        exact conj_of_commute' (hsup _ (Or.inr (minusXS_mem hirr (hJS' hS) p)) _)
      · exact oaNM_conj_lastS hirr Θ ρ₀ ρ₁ hS (by simp) (by simp) j p

theorem FrameHypM.weyl (i j : Fin (m + 4 + 2 - 1)) (hij : i.val < j.val) :
    ∃ ñ : Fin (m + 4 + 2 - 1) → G, ∀ k, (k = i ∨ k = j) →
      ∀ γ ∈ pairRoots (minusDatum (m + 4 + 2) hirr) i j,
        (MinusLong (m + 4 + 2) γ → ∀ a, ñ k * oaPsiL Θ φ₀ φ₁ γ a * (ñ k)⁻¹ =
          oaPsiL Θ φ₀ φ₁ ((ΦMinus (m + 4 + 2) hirr).refl k γ) a) ∧
        (MinusShort (m + 4 + 2) γ → ∀ p, ñ k * oaPsiS hirr Θ γ p * (ñ k)⁻¹ =
          oaPsiS hirr Θ ((ΦMinus (m + 4 + 2) hirr).refl k γ)
            (if k.val + 2 = m + 4 + 2 then planeRefl b c planeOne p else p)) := by
  refine ⟨oaNM hirr Θ ρ₀ ρ₁, fun k hk γ hγ => ?_⟩
  obtain ⟨hγR, hγs⟩ := hγ
  change γ ∈ RootSystem.roots (isFiniteType_cartanB (m + 4 + 2 - 1)) ∅ at hγR
  change (MinusLong (m + 4 + 2) γ → ∀ a, oaNM hirr Θ ρ₀ ρ₁ k * oaPsiL Θ φ₀ φ₁ γ a *
      (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ = oaPsiL Θ φ₀ φ₁ (reflection (cartanB (m + 4 + 2 - 1)) k γ) a) ∧
    (MinusShort (m + 4 + 2) γ → ∀ p, oaNM hirr Θ ρ₀ ρ₁ k * oaPsiS hirr Θ γ p *
      (oaNM hirr Θ ρ₀ ρ₁ k)⁻¹ = oaPsiS hirr Θ (reflection (cartanB (m + 4 + 2 - 1)) k γ)
        (if k.val + 2 = m + 4 + 2 then planeRefl b c planeOne p else p))
  rcases node_casesM j with rfl | rfl | ⟨j', rfl⟩
  · exact absurd hij (show ¬ (i.val < 0) by omega)
  · rcases node_casesM i with rfl | rfl | ⟨i', rfl⟩
    · exact ⟨fun _ a => H.weyl01 hγR hγs hk a,
        fun hS => absurd (minusLong_pair01 hγR hγs) hS.not_long⟩
    · exact absurd hij (show ¬ (1 < 1) by omega)
    · exact absurd hij (show ¬ (i'.val + 2 < 1) by omega)
  · rcases node_casesM i with rfl | rfl | ⟨i', rfl⟩
    · exact H.weyl0j j' hγR hγs hk
    · by_cases hj' : j'.val = 0
      · obtain rfl : j' = y0 m := Fin.ext hj'
        exact ⟨fun _ a => H.weyl12 hγR hγs hk a,
          fun hS => absurd (minusLong_pair12 hγR hγs) hS.not_long⟩
      · exact H.weyl1j j' hj' hγR hγs hk
    · have h0 : γ ⟨0, show 0 < m + 4 + 2 - 1 by omega⟩ = 0 :=
        hγs _ (Fin.ne_of_val_ne (show (0 : ℕ) ≠ i'.val + 2 by omega))
          (Fin.ne_of_val_ne (show (0 : ℕ) ≠ j'.val + 2 by omega))
      have h1 : γ ⟨1, show 1 < m + 4 + 2 - 1 by omega⟩ = 0 :=
        hγs _ (Fin.ne_of_val_ne (show (1 : ℕ) ≠ i'.val + 2 by omega))
          (Fin.ne_of_val_ne (show (1 : ℕ) ≠ j'.val + 2 by omega))
      rcases hk with rfl | rfl
      · exact ⟨fun hL a => oaNM_conj_lastL hirr Θ φ₀ φ₁ ρ₀ ρ₁ hL h0 h1 i' a,
          fun hS p => oaNM_conj_lastS hirr Θ ρ₀ ρ₁ hS h0 h1 i' p⟩
      · exact ⟨fun hL a => oaNM_conj_lastL hirr Θ φ₀ φ₁ ρ₀ ρ₁ hL h0 h1 j' a,
          fun hS p => oaNM_conj_lastS hirr Θ ρ₀ ρ₁ hS h0 h1 j' p⟩

end FrameWeylM

theorem exists_upB_of_B2 {m : ℕ} (i : Fin (m + 4 + 2 - 1)) (h : i.val + 3 = m + 4 + 2) :
    ∃ k : Fin (m + 4 - 1), ∃ hk : k.val + 1 < m + 4 - 1, k.val + 3 = m + 4 ∧ i = upB k ∧
      (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) = upB ⟨k.val + 1, hk⟩ := by
  rcases node_casesM i with rfl | rfl | ⟨k, rfl⟩
  · exact absurd h (show ¬ (0 + 3 = m + 4 + 2) by omega)
  · exact absurd h (show ¬ (1 + 3 = m + 4 + 2) by omega)
  · have h' : k.val + 2 + 3 = m + 4 + 2 := h
    exact ⟨k, by omega, by omega, rfl, upB_succ k (by omega)⟩

section FrameMainM

variable {G : Type} [Group G] {m : ℕ} {F : Type} [Field F] [CharP F 2] {b c : F}
  {hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0} {Θ : spinGroup (quadMinus (m + 4) F b c) →* G}
  {φ₀ φ₁ : SpecialLinearGroup (Fin 3) F →* G} {ρ₀ ρ₁ : SpecialLinearGroup (Fin 2) F →* G}

variable (hirr Θ φ₀ φ₁) in
theorem oaPsiM_B2 (i : Fin (m + 4 + 2 - 1)) (h : i.val + 3 = m + 4 + 2) (p q : Fin 2 → F)
    (s t : F) :
    ⁅oaPsiS hirr Θ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) p,
        oaPsiL Θ φ₀ φ₁ (Pi.single i 1) s⁆ =
      oaPsiS hirr Θ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1)
          (s • p) *
        oaPsiL Θ φ₀ φ₁
          (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1)
          (s * planeNorm b c p) ∧
    ⁅oaPsiS hirr Θ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) p,
        oaPsiS hirr Θ
          (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) q⁆ =
      oaPsiL Θ φ₀ φ₁
        (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1)
        (polarPlane b c p q) ∧
    Commute (oaPsiS hirr Θ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) p)
      (oaPsiL Θ φ₀ φ₁
        (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) s) ∧
    Commute (oaPsiS hirr Θ
        (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) p)
      (oaPsiL Θ φ₀ φ₁
        (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) s) ∧
    Commute (oaPsiS hirr Θ
        (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) p)
      (oaPsiL Θ φ₀ φ₁ (Pi.single i 1) s) ∧
    Commute (oaPsiL Θ φ₀ φ₁
        (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) s)
      (oaPsiL Θ φ₀ φ₁ (Pi.single i 1) t) := by
  obtain ⟨k, hk1, hk, rfl, e1⟩ := exists_upB_of_B2 i h
  rw [e1]
  simp only [oaPsiS_up, oaPsiL_up, oaPsiS_up_add, oaPsiL_up_add_two]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_commutatorElement, minus_comm_B2 hirr hk, map_mul]
  · rw [← map_commutatorElement, minus_comm_B2' hirr hk]
  · exact (minus_commute_B2_b_2ab hirr hk p s).map Θ
  · exact (minus_commute_B2_ab_2ab hirr hk p s).map Θ
  · exact (minus_commute_B2_ab_a hirr hk p s).map Θ
  · exact (minus_commute_B2_2ab_a hk s t).map Θ

variable (H : FrameHypM hirr Θ φ₀ φ₁ ρ₀ ρ₁)
include H

theorem FrameHypM.commA2 (i : Fin (m + 4 + 2 - 1)) (h : i.val + 3 < m + 4 + 2) (s t : F) :
    ⁅oaPsiL Θ φ₀ φ₁ (Pi.single i 1) s,
      oaPsiL Θ φ₀ φ₁ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) t⁆ =
    oaPsiL Θ φ₀ φ₁ (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1)
      (s * t) := by
  rcases node_casesM i with rfl | rfl | ⟨k, rfl⟩
  · show ⁅oaPsiL Θ φ₀ φ₁ (d0 m) s, oaPsiL Θ φ₀ φ₁ (d1 m) t⁆ =
      oaPsiL Θ φ₀ φ₁ (d0 m + d1 m) (s * t)
    rw [oaPsiL_d0, oaPsiL_d1, oaPsiL_d01, ← map_commutatorElement,
      tv_comm (by decide) (by decide) (by decide)]
  · show ⁅oaPsiL Θ φ₀ φ₁ (d1 m) s, oaPsiL Θ φ₀ φ₁ (d2 m) t⁆ =
      oaPsiL Θ φ₀ φ₁ (d1 m + d2 m) (s * t)
    rw [H.w_d1, H.w_d2, oaPsiL_d12, ← map_commutatorElement,
      tv_comm (by decide) (by decide) (by decide)]
  · have h' : k.val + 2 + 3 < m + 4 + 2 := h
    have hk : k.val + 1 < m + 4 - 1 := by omega
    rw [upB_succ k hk, oaPsiL_up, oaPsiL_up, oaPsiL_up_add, ← map_commutatorElement,
      minus_comm_A2 (n := m + 4) (i := k) (by omega)]

theorem FrameHypM.commuteA2l (i : Fin (m + 4 + 2 - 1)) (h : i.val + 3 < m + 4 + 2) (s t : F) :
    Commute (oaPsiL Θ φ₀ φ₁ (Pi.single i 1) s)
      (oaPsiL Θ φ₀ φ₁
        (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) t) := by
  rcases node_casesM i with rfl | rfl | ⟨k, rfl⟩
  · show Commute (oaPsiL Θ φ₀ φ₁ (d0 m) s) (oaPsiL Θ φ₀ φ₁ (d0 m + d1 m) t)
    rw [oaPsiL_d0, oaPsiL_d01]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₀
  · show Commute (oaPsiL Θ φ₀ φ₁ (d1 m) s) (oaPsiL Θ φ₀ φ₁ (d1 m + d2 m) t)
    rw [H.w_d1, oaPsiL_d12]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₁
  · have h' : k.val + 2 + 3 < m + 4 + 2 := h
    have hk : k.val + 1 < m + 4 - 1 := by omega
    rw [upB_succ k hk, oaPsiL_up, oaPsiL_up_add]
    exact (minus_commute_A2_left (n := m + 4) (b := b) (c := c) (i := k) (by omega) s t).map Θ

theorem FrameHypM.commuteA2r (i : Fin (m + 4 + 2 - 1)) (h : i.val + 3 < m + 4 + 2) (s t : F) :
    Commute
      (oaPsiL Θ φ₀ φ₁
        (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) s)
      (oaPsiL Θ φ₀ φ₁ (Pi.single (⟨i.val + 1, by omega⟩ : Fin (m + 4 + 2 - 1)) 1) t) := by
  rcases node_casesM i with rfl | rfl | ⟨k, rfl⟩
  · show Commute (oaPsiL Θ φ₀ φ₁ (d0 m + d1 m) s) (oaPsiL Θ φ₀ φ₁ (d1 m) t)
    rw [oaPsiL_d01, oaPsiL_d1]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₀
  · show Commute (oaPsiL Θ φ₀ φ₁ (d1 m + d2 m) s) (oaPsiL Θ φ₀ φ₁ (d2 m) t)
    rw [oaPsiL_d12, H.w_d2]
    exact (tv_commute (by decide) (by decide) (by decide) (by decide) s t).map φ₁
  · have h' : k.val + 2 + 3 < m + 4 + 2 := h
    have hk : k.val + 1 < m + 4 - 1 := by omega
    rw [upB_succ k hk, oaPsiL_up, oaPsiL_up_add]
    exact (minus_commute_A2_right (n := m + 4) (b := b) (c := c) (i := k) (by omega) s t).map Θ

theorem FrameHypM.commuteA1A1L (i j : Fin (m + 4 + 2 - 1)) (hij : i.val + 2 ≤ j.val)
    (hj : j.val + 2 < m + 4 + 2) (s t : F) :
    Commute (oaPsiL Θ φ₀ φ₁ (Pi.single i 1) s) (oaPsiL Θ φ₀ φ₁ (Pi.single j 1) t) := by
  rcases node_casesM j with rfl | rfl | ⟨j', rfl⟩
  · exact absurd hij (show ¬ (i.val + 2 ≤ 0) by omega)
  · exact absurd hij (show ¬ (i.val + 2 ≤ 1) by omega)
  · have hj' : j'.val + 2 + 2 < m + 4 + 2 := hj
    rw [oaPsiL_up]
    rcases node_casesM i with rfl | rfl | ⟨i', rfl⟩
    · show Commute (oaPsiL Θ φ₀ φ₁ (d0 m) s) _
      rw [H.v_d0]
      exact H.V _ _
    · show Commute (oaPsiL Θ φ₀ φ₁ (d1 m) s) _
      have h' : 1 + 2 ≤ j'.val + 2 := hij
      rw [H.v_d1]
      exact (H.commute_long j' (by omega) (by omega) _ _).1
    · have h' : i'.val + 2 + 2 ≤ j'.val + 2 := hij
      rw [oaPsiL_up]
      exact (minus_commute_A1A1_long (n := m + 4) (b := b) (c := c) (i := i') (j := j')
        (by omega) (by omega) s t).map Θ

theorem FrameHypM.commuteA1A1S (i k : Fin (m + 4 + 2 - 1)) (hik : i.val + 2 ≤ k.val)
    (hk : k.val + 2 = m + 4 + 2) (s : F) (p : Fin 2 → F) :
    Commute (oaPsiL Θ φ₀ φ₁ (Pi.single i 1) s) (oaPsiS hirr Θ (Pi.single k 1) p) := by
  rcases node_casesM k with rfl | rfl | ⟨k', rfl⟩
  · exact absurd hik (show ¬ (i.val + 2 ≤ 0) by omega)
  · exact absurd hik (show ¬ (i.val + 2 ≤ 1) by omega)
  · have hk' : k'.val + 2 + 2 = m + 4 + 2 := hk
    rw [oaPsiS_up]
    rcases node_casesM i with rfl | rfl | ⟨i', rfl⟩
    · show Commute (oaPsiL Θ φ₀ φ₁ (d0 m) s) _
      rw [H.v_d0]
      exact H.V _ _
    · show Commute (oaPsiL Θ φ₀ φ₁ (d1 m) s) _
      have h' : 1 + 2 ≤ k'.val + 2 := hik
      rw [H.v_d1]
      exact (H.commute_short k' (by omega) (by omega) _ _).1
    · have h' : i'.val + 2 + 2 ≤ k'.val + 2 := hik
      rw [oaPsiL_up]
      exact (minus_commute_A1A1_short hirr (i := i') (k := k') (by omega) (by omega) s p).map Θ

theorem FrameHypM.rankL (k : Fin (m + 4 + 2 - 1)) (hk : k.val + 2 < m + 4 + 2) :
    ∃ Θk : SpecialLinearGroup (Fin 2) F →* G,
      (∀ x, Θk (sl2Upper x) = oaPsiL Θ φ₀ φ₁ (Pi.single k 1) x) ∧
        ∀ x, Θk (sl2Lower x) = oaPsiL Θ φ₀ φ₁ (-Pi.single k 1) x := by
  rcases node_casesM k with rfl | rfl | ⟨k', rfl⟩
  · exact ⟨ρ₀, fun x => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact (H.v_d0 x).symm,
      fun x => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact (H.v_nd0 x).symm⟩
  · exact ⟨ρ₁, fun x => by rw [← LevisExtras.tv01_eq_sl2Upper]; exact (H.v_d1 x).symm,
      fun x => by rw [← LevisExtras.tv10_eq_sl2Lower]; exact (H.v_nd1 x).symm⟩
  · have hk' : k'.val + 2 < m + 4 := by
      have : k'.val + 2 + 2 < m + 4 + 2 := hk
      omega
    obtain ⟨φ, -, hφU, hφL⟩ := exists_sl2_minusXL (n := m + 4) (b := b) (c := c) hk'
    refine ⟨Θ.comp φ, fun x => ?_, fun x => ?_⟩
    · rw [MonoidHom.comp_apply, hφU, oaPsiL_up]
    · rw [MonoidHom.comp_apply, hφL, oaPsiL_neg_up]

omit H in
theorem oaPsiS_rankS [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (k : Fin (m + 4 + 2 - 1)) (hk : k.val + 2 = m + 4 + 2) :
    ∃ Θk : SL2E b c →* G,
      (∀ t, Θk (sl2Upper t) = oaPsiS hirr Θ (Pi.single k 1) (fieldCoord t)) ∧
        ∀ t, Θk (sl2Lower t) = oaPsiS hirr Θ (-Pi.single k 1) (starCoord t) := by
  rcases node_casesM k with rfl | rfl | ⟨k', rfl⟩
  · exact absurd hk (show ¬ (0 + 2 = m + 4 + 2) by omega)
  · exact absurd hk (show ¬ (1 + 2 = m + 4 + 2) by omega)
  · have hk' : k'.val + 2 = m + 4 := by
      have : k'.val + 2 + 2 = m + 4 + 2 := hk
      omega
    obtain ⟨φ, -, hφU, hφL⟩ := exists_sl2_minusXS hirr hk'
    refine ⟨Θ.comp φ, fun t => ?_, fun t => ?_⟩
    · rw [MonoidHom.comp_apply, hφU, oaPsiS_up]
    · rw [MonoidHom.comp_apply, hφL, oaPsiS_neg_up]

omit [CharP F 2] in
theorem FrameHypM.gen [Finite F] (hgen : ρ₀.range ⊔ ρ₁.range ⊔ Θ.range = ⊤) :
    Subgroup.closure (⋃ k : Fin (m + 4 + 2 - 1), if k.val + 2 < m + 4 + 2 then
      Set.range (oaPsiL Θ φ₀ φ₁ (Pi.single k 1)) ∪ Set.range (oaPsiL Θ φ₀ φ₁ (-Pi.single k 1))
    else Set.range (oaPsiS hirr Θ (Pi.single k 1)) ∪
      Set.range (oaPsiS hirr Θ (-Pi.single k 1))) = ⊤ := by
  set S := Subgroup.closure (⋃ k : Fin (m + 4 + 2 - 1), if k.val + 2 < m + 4 + 2 then
      Set.range (oaPsiL Θ φ₀ φ₁ (Pi.single k 1)) ∪ Set.range (oaPsiL Θ φ₀ φ₁ (-Pi.single k 1))
    else Set.range (oaPsiS hirr Θ (Pi.single k 1)) ∪
      Set.range (oaPsiS hirr Θ (-Pi.single k 1))) with hS
  have hmemL : ∀ k : Fin (m + 4 + 2 - 1), k.val + 2 < m + 4 + 2 → ∀ x,
      oaPsiL Θ φ₀ φ₁ (Pi.single k 1) x ∈ S ∧ oaPsiL Θ φ₀ φ₁ (-Pi.single k 1) x ∈ S :=
    fun k hk x => by
      refine ⟨Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, ?_⟩),
        Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      · rw [ite_eq_left hk]
        exact Or.inl ⟨x, rfl⟩
      · rw [ite_eq_left hk]
        exact Or.inr ⟨x, rfl⟩
  have hmemS : ∀ k : Fin (m + 4 + 2 - 1), ¬ k.val + 2 < m + 4 + 2 → ∀ p,
      oaPsiS hirr Θ (Pi.single k 1) p ∈ S ∧ oaPsiS hirr Θ (-Pi.single k 1) p ∈ S :=
    fun k hk p => by
      refine ⟨Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, ?_⟩),
        Subgroup.subset_closure (Set.mem_iUnion.2 ⟨k, ?_⟩)⟩
      · rw [ite_eq_right hk]
        exact Or.inl ⟨p, rfl⟩
      · rw [ite_eq_right hk]
        exact Or.inr ⟨p, rfl⟩
  rw [eq_top_iff, ← hgen]
  refine sup_le (sup_le ?_ ?_) ?_
  · rintro _ ⟨g, rfl⟩
    refine CaseM.sl2_mem_of_tv ρ₀ (fun x => ?_) (fun x => ?_) g
    · rw [← H.v_d0]
      exact (hmemL _ (show 0 + 2 < m + 4 + 2 by omega) x).1
    · rw [← H.v_nd0]
      exact (hmemL _ (show 0 + 2 < m + 4 + 2 by omega) x).2
  · rintro _ ⟨g, rfl⟩
    refine CaseM.sl2_mem_of_tv ρ₁ (fun x => ?_) (fun x => ?_) g
    · rw [← H.v_d1]
      exact (hmemL _ (show 1 + 2 < m + 4 + 2 by omega) x).1
    · rw [← H.v_nd1]
      exact (hmemL _ (show 1 + 2 < m + 4 + 2 by omega) x).2
  · rintro _ ⟨y, rfl⟩
    have hy : y ∈ ⨆ k, ((minusDatum (m + 4) hirr).rootGroup (Pi.single k 1) ⊔
        (minusDatum (m + 4) hirr).rootGroup (-Pi.single k 1)) := by
      rw [CaseM.iSup_rankOne_eq_top (minusDatum_isCTGroupDatum (m + 4) hirr (by omega)) rfl]
      exact Subgroup.mem_top y
    have hle : (⨆ k, ((minusDatum (m + 4) hirr).rootGroup (Pi.single k 1) ⊔
        (minusDatum (m + 4) hirr).rootGroup (-Pi.single k 1))) ≤ S.comap Θ := by
      refine iSup_le fun (k : Fin (m + 4 - 1)) => sup_le (fun z hz => ?_) (fun z hz => ?_)
      · by_cases hk : k.val + 2 < m + 4
        · obtain ⟨a, rfl⟩ := exists_minusXL_eq hirr (minusLong_single hk) hz
          have := (hmemL (upB k) (show k.val + 2 + 2 < m + 4 + 2 by omega) a).1
          rwa [oaPsiL_up] at this
        · obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr (minusShort_single (by omega)) hz
          have := (hmemS (upB k) (show ¬ (k.val + 2 + 2 < m + 4 + 2) by omega) p).1
          rwa [oaPsiS_up] at this
      · by_cases hk : k.val + 2 < m + 4
        · obtain ⟨a, rfl⟩ := exists_minusXL_eq hirr (minusLong_neg_single hk) hz
          have := (hmemL (upB k) (show k.val + 2 + 2 < m + 4 + 2 by omega) a).2
          rwa [oaPsiL_neg_up] at this
        · obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr (minusShort_neg_single (by omega)) hz
          have := (hmemS (upB k) (show ¬ (k.val + 2 + 2 < m + 4 + 2) by omega) p).2
          rwa [oaPsiS_neg_up] at this
    exact hle hy

theorem FrameHypM.isMinusFrame [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)]
    (hgen : ρ₀.range ⊔ ρ₁.range ⊔ Θ.range = ⊤) (hnt : ρ₀ (tv 0 1 1) ≠ 1) :
    IsMinusFrame (m + 4 + 2) hirr (oaPsiL Θ φ₀ φ₁) (oaPsiS hirr Θ) where
  addL _ _ γ _ _ x y := oaPsiL_add Θ φ₀ φ₁ γ x y
  addS _ _ γ _ _ p q := oaPsiS_add Θ hirr γ p q
  commA2 := H.commA2
  commuteA2l := H.commuteA2l
  commuteA2r := H.commuteA2r
  commB2 i h p s := (oaPsiM_B2 hirr Θ φ₀ φ₁ i h p p s s).1
  commB2' i h p q := (oaPsiM_B2 hirr Θ φ₀ φ₁ i h p q 0 0).2.1
  commuteB2_b_2ab i h p s := (oaPsiM_B2 hirr Θ φ₀ φ₁ i h p p s s).2.2.1
  commuteB2_ab_2ab i h p s := (oaPsiM_B2 hirr Θ φ₀ φ₁ i h p p s s).2.2.2.1
  commuteB2_ab_a i h p s := (oaPsiM_B2 hirr Θ φ₀ φ₁ i h p p s s).2.2.2.2.1
  commuteB2_2ab_a i h s t := (oaPsiM_B2 hirr Θ φ₀ φ₁ i h 0 0 s t).2.2.2.2.2
  commuteA1A1L := H.commuteA1A1L
  commuteA1A1S := H.commuteA1A1S
  weyl := H.weyl
  rankL := H.rankL
  rankS := oaPsiS_rankS
  gen := H.gen hgen
  nt := ⟨⟨0, by omega⟩, show 0 + 2 < m + 4 + 2 by omega, 1, by
    rw [show (Pi.single (⟨0, by omega⟩ : Fin (m + 4 + 2 - 1)) 1 : Fin (m + 4 + 2 - 1) → ℤ) =
      d0 m from rfl, H.v_d0]
    exact hnt⟩

end FrameMainM

end CFSG.Timmesfeld.ARS.CaseOANSL

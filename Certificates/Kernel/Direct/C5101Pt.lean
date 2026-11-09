module

public import CFSG.GH74.GLS.Stage4.Q9.PermCharInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import CFSG.GH74.GLS.Stage4.Q9.ModelBase
import Mathlib.Tactic.FinCases

public section

namespace CertificateChecks.KernelDirect.C5101

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4 CFSG.GH74.GLS.Stage4.Q9

@[expose] def ptFacts (l : Lg) (a : ℤ) : Prop :=
  a ∈ ({-1, 0, 1, 9} : Finset ℤ) ∧ (a = 9 ↔ l = 1 ∨ l = innerL minusOne) ∧
    (parityL l ≠ 1 → a ∈ ({-1, 1} : Finset ℤ)) ∧ a = aByOrder (decide (parityL l = 1)) (ordL l)

instance (l : Lg) (a : ℤ) : Decidable (ptFacts l a) := by
  unfold ptFacts
  infer_instance

@[expose] def ptP (a : F9) (ε : Multiplicative (ZMod 2)) : Prop :=
  ∀ b c d : F9, ∀ h : a * d - b * c = 1,
    ptFacts ⟨⟨!![a, b; c, d], (Matrix.det_fin_two_of a b c d).trans h⟩, ε⟩
      (aTabFast ⟨⟨!![a, b; c, d], (Matrix.det_fin_two_of a b c d).trans h⟩, ε⟩)

instance (a : F9) (ε : Multiplicative (ZMod 2)) : Decidable (ptP a ε) := by
  unfold ptP
  infer_instance

theorem forall_Lg {P : Lg → Prop}
    (h1 : ∀ a b c d : F9, ∀ h : a * d - b * c = 1,
      P ⟨⟨!![a, b; c, d], (Matrix.det_fin_two_of a b c d).trans h⟩, 1⟩)
    (h2 : ∀ a b c d : F9, ∀ h : a * d - b * c = 1,
      P ⟨⟨!![a, b; c, d], (Matrix.det_fin_two_of a b c d).trans h⟩, Multiplicative.ofAdd 1⟩) :
    ∀ l, P l := by
  rintro ⟨⟨M, hM⟩, ε⟩
  have h : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by rw [← Matrix.det_fin_two]; exact hM
  have hx : (⟨M, hM⟩ : SL2) =
      ⟨!![M 0 0, M 0 1; M 1 0, M 1 1], (Matrix.det_fin_two_of _ _ _ _).trans h⟩ :=
    Subtype.ext (Matrix.eta_fin_two M)
  rw [hx]
  rcases PermChar.right_cases ε with rfl | rfl
  · exact h1 _ _ _ _ h
  · exact h2 _ _ _ _ h

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_00_one : ptP ⟨0, 0⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_01_one : ptP ⟨0, 1⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_02_one : ptP ⟨0, 2⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_10_one : ptP ⟨1, 0⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_11_one : ptP ⟨1, 1⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_12_one : ptP ⟨1, 2⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_20_one : ptP ⟨2, 0⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_21_one : ptP ⟨2, 1⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_22_one : ptP ⟨2, 2⟩ (1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_00_neg : ptP ⟨0, 0⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_01_neg : ptP ⟨0, 1⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_02_neg : ptP ⟨0, 2⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_10_neg : ptP ⟨1, 0⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_11_neg : ptP ⟨1, 1⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_12_neg : ptP ⟨1, 2⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_20_neg : ptP ⟨2, 0⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_21_neg : ptP ⟨2, 1⟩ (Multiplicative.ofAdd 1) := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ptP_22_neg : ptP ⟨2, 2⟩ (Multiplicative.ofAdd 1) := by decide +kernel

theorem ptFacts_aTabFast : ∀ l : Lg, ptFacts l (aTabFast l) := by
  refine forall_Lg (P := fun l => ptFacts l (aTabFast l)) ?_ ?_
  · intro a
    rcases a with ⟨r, i⟩
    fin_cases r <;> fin_cases i
    exacts [ptP_00_one, ptP_01_one, ptP_02_one, ptP_10_one, ptP_11_one, ptP_12_one, ptP_20_one, ptP_21_one, ptP_22_one]
  · intro a
    rcases a with ⟨r, i⟩
    fin_cases r <;> fin_cases i
    exacts [ptP_00_neg, ptP_01_neg, ptP_02_neg, ptP_10_neg, ptP_11_neg, ptP_12_neg, ptP_20_neg, ptP_21_neg, ptP_22_neg]


end CertificateChecks.KernelDirect.C5101

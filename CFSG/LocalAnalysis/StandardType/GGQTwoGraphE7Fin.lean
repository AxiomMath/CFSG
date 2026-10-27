module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Data.ZMod.Basic
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType

@[expose] def ggg7_C (i j : Fin 7) : ZMod 3 :=
  if i = j then 2
  else if (i.val = 0 ∧ j.val = 2) ∨ (j.val = 0 ∧ i.val = 2) ∨
      (i.val = 1 ∧ j.val = 3) ∨ (j.val = 1 ∧ i.val = 3) ∨
      (2 ≤ i.val ∧ i.val + 1 = j.val) ∨ (2 ≤ j.val ∧ j.val + 1 = i.val)
  then -1 else 0

theorem ggg7_C_eq (i j : Fin 7) : ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) = ggg7_C i j := by
  simp only [CartanMatrix.E, Matrix.of_apply, ggg7_C]
  split_ifs <;> simp

@[expose] def ggg7_S (j : Fin 7) (v : Fin 7 → ZMod 3) : Fin 7 → ZMod 3 :=
  v - (∑ k, ggg7_C j k * v k) • Pi.single j 1

@[expose] def ggg7_word (l : List (Fin 7)) (v : Fin 7 → ZMod 3) : Fin 7 → ZMod 3 :=
  l.foldl (fun w j => ggg7_S j w) v

@[expose] def ggg7_y : Fin 7 → ZMod 3 := ![1, 1, 0, 2, 0, 1, 2]

@[expose] def ggg7_z0 (c₀ t : ZMod 3) : Fin 7 → ZMod 3 :=
  ![t, t, -c₀, 2 * t - 2 * c₀, 0, t - c₀, 2 * t - 2 * c₀]

@[expose] def ggg7_tau : Fin 7 → Fin 7 := ![0, 2, 1, 3, 4, 5, 6]

@[expose] def ggg7_img (c₀ t : ZMod 3) : Fin 7 → (Fin 7 → ZMod 3) :=
  ![ggg7_z0 c₀ t, c₀ • Pi.single 2 1, c₀ • Pi.single 1 1, c₀ • Pi.single 3 1,
    c₀ • Pi.single 4 1, c₀ • Pi.single 5 1, c₀ • Pi.single 6 1]

@[expose] def ggg7_T (c₀ t : ZMod 3) (v : Fin 7 → ZMod 3) : Fin 7 → ZMod 3 :=
  ∑ k, v k • ggg7_img c₀ t k

@[expose] def ggg7_N (l : List (Fin 7)) (c₀ t : ZMod 3) (v : Fin 7 → ZMod 3) : Fin 7 → ZMod 3 :=
  ggg7_word l (ggg7_T c₀ t (ggg7_S 0 (ggg7_T c₀ t (ggg7_word l.reverse v))))

@[expose] def ggg7_phi : List (Fin 7 → ZMod 3) :=
  [![0, 0, 0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0, 0, 2],
    ![0, 0, 0, 0, 0, 1, 0],
    ![0, 0, 0, 0, 0, 1, 1],
    ![0, 0, 0, 0, 0, 2, 0],
    ![0, 0, 0, 0, 0, 2, 2],
    ![0, 0, 0, 0, 1, 0, 0],
    ![0, 0, 0, 0, 1, 1, 0],
    ![0, 0, 0, 0, 1, 1, 1],
    ![0, 0, 0, 0, 2, 0, 0],
    ![0, 0, 0, 0, 2, 2, 0],
    ![0, 0, 0, 0, 2, 2, 2],
    ![0, 0, 0, 1, 0, 0, 0],
    ![0, 0, 0, 1, 1, 0, 0],
    ![0, 0, 0, 1, 1, 1, 0],
    ![0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 2, 2, 2, 0],
    ![0, 0, 0, 2, 2, 2, 2],
    ![0, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 1, 0, 0, 0],
    ![0, 0, 1, 1, 1, 0, 0],
    ![0, 0, 1, 1, 1, 1, 0],
    ![0, 0, 1, 1, 1, 1, 1],
    ![0, 0, 2, 0, 0, 0, 0],
    ![0, 0, 2, 2, 0, 0, 0],
    ![0, 0, 2, 2, 2, 0, 0],
    ![0, 0, 2, 2, 2, 2, 0],
    ![0, 0, 2, 2, 2, 2, 2],
    ![0, 1, 0, 0, 0, 0, 0],
    ![0, 1, 0, 1, 0, 0, 0],
    ![0, 1, 0, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0, 0],
    ![0, 1, 1, 1, 1, 0, 0],
    ![0, 1, 1, 1, 1, 1, 0],
    ![0, 1, 1, 1, 1, 1, 1],
    ![0, 1, 1, 2, 1, 0, 0],
    ![0, 1, 1, 2, 1, 1, 0],
    ![0, 1, 1, 2, 1, 1, 1],
    ![0, 1, 1, 2, 2, 1, 0],
    ![0, 1, 1, 2, 2, 1, 1],
    ![0, 1, 1, 2, 2, 2, 1],
    ![0, 2, 0, 0, 0, 0, 0],
    ![0, 2, 0, 2, 0, 0, 0],
    ![0, 2, 0, 2, 2, 0, 0],
    ![0, 2, 0, 2, 2, 2, 0],
    ![0, 2, 0, 2, 2, 2, 2],
    ![0, 2, 2, 1, 1, 1, 2],
    ![0, 2, 2, 1, 1, 2, 0],
    ![0, 2, 2, 1, 1, 2, 2],
    ![0, 2, 2, 1, 2, 0, 0],
    ![0, 2, 2, 1, 2, 2, 0],
    ![0, 2, 2, 1, 2, 2, 2],
    ![0, 2, 2, 2, 0, 0, 0],
    ![0, 2, 2, 2, 2, 0, 0],
    ![0, 2, 2, 2, 2, 2, 0],
    ![0, 2, 2, 2, 2, 2, 2]]

theorem ggg7_phi_simple : ∀ j : Fin 7, j ≠ 0 → (Pi.single j 1 : Fin 7 → ZMod 3) ∈ ggg7_phi := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggg7_phi_closed : ∀ v ∈ ggg7_phi, ∀ j : Fin 7, j ≠ 0 → ggg7_S j v ∈ ggg7_phi := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggg7_phi_neg : ∀ v ∈ ggg7_phi, -v ∈ ggg7_phi := by
  decide +kernel

theorem ggg7_img_ne (c₀ t : ZMod 3) (k : Fin 7) (hk : k ≠ 0) :
    ggg7_img c₀ t k = c₀ • Pi.single (ggg7_tau k) 1 := by
  fin_cases k <;> simp [ggg7_img, ggg7_tau] at hk ⊢

theorem ggg7_T_y (c₀ t : ZMod 3) (hc : c₀ = 1 ∨ c₀ = 2) (ht : t = 1 ∨ t = 2) :
    ggg7_T c₀ t ggg7_y = t • ggg7_y := by
  rcases hc with rfl | rfl <;> rcases ht with rfl | rfl <;> decide +kernel

theorem ggg7_eta (v : Fin 7 → ZMod 3) : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6] := by
  funext i; fin_cases i <;> rfl

@[expose] noncomputable def ggg7_Tl (c₀ t : ZMod 3) :
    (Fin 7 → ZMod 3) →ₗ[ZMod 3] (Fin 7 → ZMod 3) :=
  Fintype.linearCombination (ZMod 3) (ggg7_img c₀ t)

theorem ggg7_Tl_apply (c₀ t : ZMod 3) (v : Fin 7 → ZMod 3) : ggg7_Tl c₀ t v = ggg7_T c₀ t v := by
  simp [ggg7_Tl, ggg7_T, Fintype.linearCombination_apply]

theorem ggg7_T_single (c₀ t : ZMod 3) (k : Fin 7) :
    ggg7_T c₀ t (Pi.single k 1) = ggg7_img c₀ t k := by
  rw [← ggg7_Tl_apply]
  simp [ggg7_Tl]

theorem ggg7_T_involutive_single (c₀ t : ZMod 3) (hc : c₀ = 1 ∨ c₀ = 2) (ht : t = 1 ∨ t = 2)
    (k : Fin 7) : ggg7_T c₀ t (ggg7_img c₀ t k) = Pi.single k 1 := by
  rcases hc with rfl | rfl <;> rcases ht with rfl | rfl <;> fin_cases k <;> decide +kernel

theorem ggg7_T_involutive (c₀ t : ZMod 3) (hc : c₀ = 1 ∨ c₀ = 2) (ht : t = 1 ∨ t = 2)
    (v : Fin 7 → ZMod 3) : ggg7_T c₀ t (ggg7_T c₀ t v) = v := by
  have h : (ggg7_Tl c₀ t).comp (ggg7_Tl c₀ t) = LinearMap.id := by
    refine (Pi.basisFun (ZMod 3) (Fin 7)).ext fun k => ?_
    simp only [Pi.basisFun_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [ggg7_Tl_apply, ggg7_Tl_apply, ggg7_T_single, ggg7_T_involutive_single c₀ t hc ht k]
  have := LinearMap.congr_fun h v
  simpa [ggg7_Tl_apply] using this

theorem ggg7_y_unique (v : Fin 7 → ZMod 3)
    (h : ∀ j : Fin 7, j ≠ 0 → ∑ k, ggg7_C j k * v k = 0) :
    v = 0 ∨ v = ggg7_y ∨ v = (2 : ZMod 3) • ggg7_y := by
  have key : ∀ a b c d e f g : ZMod 3,
      (∀ j : Fin 7, j ≠ 0 → ∑ k, ggg7_C j k * (![a, b, c, d, e, f, g] : Fin 7 → ZMod 3) k = 0) →
      (![a, b, c, d, e, f, g] : Fin 7 → ZMod 3) = 0 ∨
        (![a, b, c, d, e, f, g] : Fin 7 → ZMod 3) = ggg7_y ∨
        (![a, b, c, d, e, f, g] : Fin 7 → ZMod 3) = (2 : ZMod 3) • ggg7_y := by
    decide +kernel
  rw [ggg7_eta v] at h ⊢
  exact key _ _ _ _ _ _ _ h

theorem ggg7_cert (c₀ t : ZMod 3) (hc : c₀ = 1 ∨ c₀ = 2) (ht : t = 1 ∨ t = 2) :
    ∃ (l : List (Fin 7)) (i : Fin 7), i ≠ 0 ∧
      (∀ s : ZMod 3, ggg7_N l c₀ t (s • ggg7_y) = s • ggg7_y) ∧
      ggg7_N l c₀ t (Pi.single i 1) ∉ ggg7_phi := by
  rcases hc with rfl | rfl <;> rcases ht with rfl | rfl
  · exact ⟨[1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0], 2, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[0], 1, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[0], 1, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[1, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0], 2, by decide, by decide +kernel, by decide +kernel⟩

end CFSG.StandardType

end

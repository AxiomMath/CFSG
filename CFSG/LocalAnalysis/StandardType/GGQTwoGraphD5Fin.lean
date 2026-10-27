module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.Data.ZMod.Basic
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType

@[expose] def ggg5_C : Fin 5 → Fin 5 → ZMod 3 :=
  ![![2, 2, 0, 0, 0], ![2, 2, 2, 0, 0], ![0, 2, 2, 2, 2], ![0, 0, 2, 2, 0], ![0, 0, 2, 0, 2]]

theorem ggg5_C_eq (i j : Fin 5) : ((CartanMatrix.D 5 i j : ℤ) : ZMod 3) = ggg5_C i j := by
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.D, ggg5_C] <;> decide

@[expose] def ggg5_S (j : Fin 5) (v : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  v - (∑ k, ggg5_C j k * v k) • Pi.single j 1

@[expose] def ggg5_word (l : List (Fin 5)) (v : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  l.foldl (fun w j => ggg5_S j w) v

@[expose] def ggg5_y : Fin 5 → ZMod 3 := ![1, 1, 1, 2, 2]

@[expose] def ggg5_x : Fin 5 → ZMod 3 := ![1, 2, 0, 1, 0]

@[expose] def ggg5_pair (g gi : Fin 5 → Fin 5) : Prop :=
  (g = ![0, 3, 2, 1, 4] ∧ gi = ![0, 3, 2, 1, 4]) ∨ (g = ![0, 3, 2, 4, 1] ∧ gi = ![0, 4, 2, 1, 3]) ∨
    (g = ![0, 4, 2, 1, 3] ∧ gi = ![0, 3, 2, 4, 1])

@[expose] def ggg5_z0 (g : Fin 5 → Fin 5) (s t : ZMod 3) : Fin 5 → ZMod 3 :=
  t • ggg5_y - s • ∑ k : Fin 5, (if k = 0 then 0 else ggg5_y k • Pi.single (g k) (1 : ZMod 3))

@[expose] def ggg5_img (g : Fin 5 → Fin 5) (s t : ZMod 3) : Fin 5 → (Fin 5 → ZMod 3) :=
  fun k => if k = 0 then ggg5_z0 g s t else s • Pi.single (g k) 1

@[expose] def ggg5_T (g : Fin 5 → Fin 5) (s t : ZMod 3) (v : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  ∑ k, v k • ggg5_img g s t k

@[expose] def ggg5_N (g gi : Fin 5 → Fin 5) (l : List (Fin 5)) (s t : ZMod 3)
    (v : Fin 5 → ZMod 3) : Fin 5 → ZMod 3 :=
  ggg5_word l (ggg5_T g s t (ggg5_S 0 (ggg5_T gi s t (ggg5_word l.reverse v))))

@[expose] def ggg5_phi : List (Fin 5 → ZMod 3) :=
  [![0, 0, 0, 0, 1],
    ![0, 0, 0, 0, 2],
    ![0, 0, 1, 0, 0],
    ![0, 0, 1, 0, 1],
    ![0, 0, 2, 0, 0],
    ![0, 0, 2, 0, 2],
    ![0, 1, 0, 0, 0],
    ![0, 1, 1, 0, 0],
    ![0, 1, 1, 0, 1],
    ![0, 2, 0, 0, 0],
    ![0, 2, 2, 0, 0],
    ![0, 2, 2, 0, 2],
    ![1, 0, 0, 0, 0],
    ![1, 1, 0, 0, 0],
    ![1, 1, 1, 0, 0],
    ![1, 1, 1, 0, 1],
    ![2, 0, 0, 0, 0],
    ![2, 2, 0, 0, 0],
    ![2, 2, 2, 0, 0],
    ![2, 2, 2, 0, 2]]

theorem ggg5_phi_simple : ∀ j : Fin 5, j ≠ 3 → (Pi.single j 1 : Fin 5 → ZMod 3) ∈ ggg5_phi := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggg5_phi_closed : ∀ v ∈ ggg5_phi, ∀ j : Fin 5, j ≠ 3 → ggg5_S j v ∈ ggg5_phi := by
  decide +kernel

open scoped CFSG.Decide.Bounded in
theorem ggg5_phi_neg : ∀ v ∈ ggg5_phi, -v ∈ ggg5_phi := by
  decide +kernel

theorem ggg5_x_three : ggg5_x 3 = 1 := by decide +kernel

theorem ggg5_x_ne : ggg5_x ≠ 0 := by decide +kernel

theorem ggg5_y_ne : ggg5_y ≠ 0 := by decide +kernel

theorem ggg5_x_fixed : ∀ j : Fin 5, j ≠ 3 → ggg5_S j ggg5_x = ggg5_x := by decide +kernel

theorem ggg5_y_fixed : ∀ j : Fin 5, j ≠ 0 → ggg5_S j ggg5_y = ggg5_y := by decide +kernel

theorem ggg5_img_ne (g : Fin 5 → Fin 5) (s t : ZMod 3) (k : Fin 5) (hk : k ≠ 0) :
    ggg5_img g s t k = s • Pi.single (g k) 1 := by
  simp [ggg5_img, hk]

theorem ggg5_T_y (g gi : Fin 5 → Fin 5) (hg : ggg5_pair g gi) (s t : ZMod 3)
    (hs : s = 1 ∨ s = 2) (ht : t = 1 ∨ t = 2) : ggg5_T g s t ggg5_y = t • ggg5_y := by
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs with rfl | rfl <;>
    rcases ht with rfl | rfl <;> decide +kernel

theorem ggg5_eta (v : Fin 5 → ZMod 3) : v = ![v 0, v 1, v 2, v 3, v 4] := by
  funext i; fin_cases i <;> rfl

@[expose] noncomputable def ggg5_Tl (g : Fin 5 → Fin 5) (s t : ZMod 3) :
    (Fin 5 → ZMod 3) →ₗ[ZMod 3] (Fin 5 → ZMod 3) :=
  Fintype.linearCombination (ZMod 3) (ggg5_img g s t)

theorem ggg5_Tl_apply (g : Fin 5 → Fin 5) (s t : ZMod 3) (v : Fin 5 → ZMod 3) :
    ggg5_Tl g s t v = ggg5_T g s t v := by
  simp [ggg5_Tl, ggg5_T, Fintype.linearCombination_apply]

theorem ggg5_T_single (g : Fin 5 → Fin 5) (s t : ZMod 3) (k : Fin 5) :
    ggg5_T g s t (Pi.single k 1) = ggg5_img g s t k := by
  rw [← ggg5_Tl_apply]
  simp [ggg5_Tl]

theorem ggg5_T_inv (g gi : Fin 5 → Fin 5) (hg : ggg5_pair g gi) (s t : ZMod 3)
    (hs : s = 1 ∨ s = 2) (ht : t = 1 ∨ t = 2) (v : Fin 5 → ZMod 3) :
    ggg5_T gi s t (ggg5_T g s t v) = v := by
  have key : ∀ a b c d e : ZMod 3,
      ggg5_T gi s t (ggg5_T g s t (![a, b, c, d, e] : Fin 5 → ZMod 3)) =
        (![a, b, c, d, e] : Fin 5 → ZMod 3) := by
    rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs with rfl | rfl <;>
      rcases ht with rfl | rfl <;> decide +kernel
  rw [ggg5_eta v]
  exact key _ _ _ _ _

theorem ggg5_cert (g gi : Fin 5 → Fin 5) (hg : ggg5_pair g gi) (s t : ZMod 3)
    (hs : s = 1 ∨ s = 2) (ht : t = 1 ∨ t = 2) :
    ∃ (l : List (Fin 5)) (i : Fin 5), i ≠ 3 ∧
      (ggg5_N g gi l s t ggg5_x = ggg5_x ∨ ggg5_N g gi l s t ggg5_x = -ggg5_x) ∧
      ggg5_N g gi l s t (Pi.single i 1) ∉ ggg5_phi := by
  rcases hg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hs with rfl | rfl <;>
    rcases ht with rfl | rfl
  · exact ⟨[3, 2, 1, 4, 2, 3], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[3, 2, 1, 4, 2, 3], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[3, 2, 1, 4, 2, 3], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[3, 2, 1, 4, 2, 3], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[], 4, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[4, 2, 3], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[4, 2, 3], 0, by decide, by decide +kernel, by decide +kernel⟩
  · exact ⟨[], 4, by decide, by decide +kernel, by decide +kernel⟩

end CFSG.StandardType

end

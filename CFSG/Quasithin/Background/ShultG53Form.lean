module

public import CFSG.Quasithin.Background.ShultG53Data
public import CFSG.Quasithin.Background.ShultG53Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY Equiv

@[expose] def symmForm (β : Fin 6 → ZMod 2) (x y : V4) : ZMod 2 :=
  β 0 * (x 0 * y 1 + x 1 * y 0) + β 1 * (x 0 * y 2 + x 2 * y 0) +
    β 2 * (x 0 * y 3 + x 3 * y 0) + β 3 * (x 1 * y 2 + x 2 * y 1) +
    β 4 * (x 1 * y 3 + x 3 * y 1) + β 5 * (x 2 * y 3 + x 3 * y 2)

@[expose] def LB : Fin 2 → List (Perm (Fin 6))
  | 0 => LB_0
  | 1 => LB_1

theorem symmForm_B0 : ∀ x y : V4, symmForm ![1, 0, 0, 1, 0, 1] x y = B0 x y := by
  decide +kernel

theorem formUnique : ∀ k : Fin 2, ∀ β : Fin 6 → ZMod 2,
    (∀ σ ∈ LB k, ∀ i j : Fin 4,
      symmForm β (Matrix.mulVec (Rm k σ) (Pi.single i 1)) (Matrix.mulVec (Rm k σ) (Pi.single j 1)) =
        symmForm β (Pi.single i 1) (Pi.single j 1)) →
    β = 0 ∨ β = ![1, 0, 0, 1, 0, 1] := by
  decide +kernel

@[expose] def betaOf (b : V4 → V4 → ZMod 2) : Fin 6 → ZMod 2 :=
  ![b (Pi.single 0 1) (Pi.single 1 1), b (Pi.single 0 1) (Pi.single 2 1),
    b (Pi.single 0 1) (Pi.single 3 1), b (Pi.single 1 1) (Pi.single 2 1),
    b (Pi.single 1 1) (Pi.single 3 1), b (Pi.single 2 1) (Pi.single 3 1)]

theorem symmForm_single : ∀ β : Fin 6 → ZMod 2, ∀ i j : Fin 4,
    symmForm β (Pi.single i 1) (Pi.single j 1) =
      ![![0, β 0, β 1, β 2], ![β 0, 0, β 3, β 4], ![β 1, β 3, 0, β 5],
        ![β 2, β 4, β 5, 0]] i j := by
  decide +kernel

theorem eq_symmForm (b : V4 → V4 → ZMod 2) (h1 : ∀ x x' y, b (x + x') y = b x y + b x' y)
    (h2 : ∀ x y y', b x (y + y') = b x y + b x y') (h3 : ∀ x, b x x = 0) :
    ∀ x y, b x y = symmForm (betaOf b) x y := by
  have hchar : ∀ a c : ZMod 2, a + c = 0 → a = c := by decide
  have hsym : ∀ x y, b x y = b y x := by
    intro x y
    have h := h3 (x + y)
    rw [h1, h2, h2, h3, h3, zero_add, add_zero] at h
    exact hchar _ _ h
  have hz1 : ∀ y, b 0 y = 0 := fun y => by
    have h := h1 0 0 y
    rw [add_zero] at h
    simpa using h
  have hz2 : ∀ x, b x 0 = 0 := fun x => by
    have h := h2 x 0 0
    rw [add_zero] at h
    simpa using h
  have hbase : ∀ i j : Fin 4, b (Pi.single i 1) (Pi.single j 1) =
      ![![0, betaOf b 0, betaOf b 1, betaOf b 2], ![betaOf b 0, 0, betaOf b 3, betaOf b 4],
        ![betaOf b 1, betaOf b 3, 0, betaOf b 5],
        ![betaOf b 2, betaOf b 4, betaOf b 5, 0]] i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> first
      | exact h3 _
      | rfl
      | exact hsym _ _
  let F : V4 →+ V4 →+ ZMod 2 := AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (b x) (h2 x))
    (fun x x' => AddMonoidHom.ext fun y => h1 x x' y)
  let G : V4 →+ V4 →+ ZMod 2 := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (symmForm (betaOf b) x) (fun y y' => by
      simp only [symmForm, Pi.add_apply]
      ring))
    (fun x x' => AddMonoidHom.ext fun y => by
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, symmForm, Pi.add_apply]
      ring)
  have hFG : F = G := by
    refine AddMonoidHom.functions_ext _ _ _ fun i x => ?_
    refine AddMonoidHom.functions_ext _ _ _ fun j y => ?_
    have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases hc x with rfl | rfl
    · show b (Pi.single i 0) (Pi.single j y) = symmForm (betaOf b) (Pi.single i 0) (Pi.single j y)
      rw [Pi.single_zero, hz1]
      simp [symmForm]
    · rcases hc y with rfl | rfl
      · show b (Pi.single i 1) (Pi.single j 0) = symmForm (betaOf b) (Pi.single i 1) (Pi.single j 0)
        rw [Pi.single_zero, hz2]
        simp [symmForm]
      · show b (Pi.single i 1) (Pi.single j 1) = symmForm (betaOf b) (Pi.single i 1) (Pi.single j 1)
        rw [symmForm_single, hbase]
  intro x y
  have := congrArg (fun H : V4 →+ V4 →+ ZMod 2 => H x y) hFG
  exact this

theorem LB_sign : ∀ k : Fin 2, ∀ σ ∈ LB k, Perm.sign σ = 1 := by decide +kernel

theorem form_unique (k : Fin 2) (b : V4 → V4 → ZMod 2)
    (h1 : ∀ x x' y, b (x + x') y = b x y + b x' y) (h2 : ∀ x y y', b x (y + y') = b x y + b x y')
    (h3 : ∀ x, b x x = 0) (hinv : ∀ (g : ↥(alternatingGroup (Fin 6))) x y,
      b (ρk k g x) (ρk k g y) = b x y)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) : ∀ x y, b x y = B0 x y := by
  have hform := eq_symmForm b h1 h2 h3
  have hb := formUnique k (betaOf b) (fun σ hσ i j => by
    have hA : σ ∈ alternatingGroup (Fin 6) := Perm.mem_alternatingGroup.mpr (LB_sign k σ hσ)
    have h := hinv ⟨σ, hA⟩ (Pi.single i 1) (Pi.single j 1)
    rw [ρk_apply, ρk_apply] at h
    rw [← hform, ← hform]
    exact h)
  rcases hb with h | h
  · exfalso
    have hz : ∀ y, b (Pi.single 0 1) y = 0 := fun y => by
      rw [hform, h]
      simp [symmForm]
    have := hnd _ hz
    have h10 : (Pi.single 0 1 : V4) ≠ 0 := by decide +kernel
    exact h10 this
  · intro x y
    rw [hform, h, symmForm_B0]

end CFSG.Quasithin.ShultG53

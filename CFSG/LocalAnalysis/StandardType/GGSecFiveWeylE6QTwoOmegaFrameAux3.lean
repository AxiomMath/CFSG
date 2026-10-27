module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaFrameAux2

public section

namespace CFSG.StandardType.E6QTwo

open Module CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.StandardType.NoOffRest
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
  {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {B : LinearMap.BilinForm (ZMod 3) V}

@[expose] def bPerp0 : List (Fin Tag.E6.rank → ZMod 3) :=
  [![0, 0, 1, 2, 0, 2], ![0, 0, 1, 2, 2, 1], ![0, 0, 2, 1, 0, 1], ![0, 0, 2, 1, 1, 2],
   ![0, 1, 0, 1, 1, 1], ![0, 1, 0, 1, 2, 2], ![0, 1, 1, 0, 1, 0], ![0, 1, 2, 2, 2, 0],
   ![0, 2, 0, 2, 1, 1], ![0, 2, 0, 2, 2, 2], ![0, 2, 1, 1, 1, 0], ![0, 2, 2, 0, 2, 0],
   ![1, 0, 0, 1, 2, 0], ![1, 0, 1, 0, 1, 1], ![1, 0, 1, 0, 2, 2], ![1, 0, 2, 2, 1, 0],
   ![1, 1, 1, 1, 0, 0], ![1, 2, 1, 2, 0, 0], ![2, 0, 0, 2, 1, 0], ![2, 0, 1, 1, 2, 0],
   ![2, 0, 2, 0, 1, 1], ![2, 0, 2, 0, 2, 2], ![2, 1, 2, 1, 0, 0], ![2, 2, 2, 2, 0, 0]]

theorem bPerp0_spec :
    ∀ c : Fin Tag.E6.rank → ZMod 3, c ∈ bPerp0 ↔ kDotP 3 c = 0 ∧ f6 c c = 2 ∧ f6 c bX0 = 0 := by
  decide +kernel

@[expose] def frameVec (c z1 z2 z3 : Fin Tag.E6.rank → ZMod 3) :
    Fin 5 → (Fin Tag.E6.rank → ZMod 3) :=
  ![bX0, c, z1, z2, z3]

@[expose] def frameGramOk (g : Fin 5 → (Fin Tag.E6.rank → ZMod 3)) : Bool :=
  (List.ofFn fun i : Fin 5 =>
    (List.ofFn fun j : Fin 5 =>
      decide (f6 (g i) (g j) = if i = j then 2 else 0)).all id).all id

theorem frameGramOk_spec {g : Fin 5 → (Fin Tag.E6.rank → ZMod 3)}
    (h : frameGramOk g = true) :
    ∀ i j : Fin 5, f6 (g i) (g j) = if i = j then 2 else 0 := by
  intro i j
  have h1 : (List.ofFn fun j : Fin 5 =>
      decide (f6 (g i) (g j) = if i = j then 2 else 0)).all id = true :=
    (List.all_eq_true.mp h) _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have h2 : decide (f6 (g i) (g j) = if i = j then 2 else 0) = true :=
    (List.all_eq_true.mp h1) _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  exact of_decide_eq_true h2

theorem bFrameCheck :
    ∀ c ∈ bPerp0, ∃ z1 ∈ bPerp0, ∃ z2 ∈ bPerp0, ∃ z3 ∈ bPerp0,
      f6 c z1 = 0 ∧ f6 c z2 = 0 ∧ f6 c z3 = 0 ∧
        f6 z1 z2 = 0 ∧ f6 z1 z3 = 0 ∧ f6 z2 z3 = 0 ∧
          frameGramOk (frameVec c z1 z2 z3) = true := by
  open scoped CFSG.Decide.Bounded in
  decide +kernel

theorem exists_frame_of_perp (hP : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hV : Nat.card V = 3 ^ 5) (hB : ∀ i v, B (h i) v = α i v) (hα : ∀ i, α i (h i) = 2)
    {x y : V} (hx : B x x = 1) (hy : B y y = 1) (hxy : B x y = 0) :
    ∃ f : Fin 5 → V, (∀ i j, B (f i) (f j) = if i = j then 1 else 0) ∧ f 0 = x ∧ f 1 = y := by
  obtain ⟨X0, hX0⟩ := exists_cv_eq (α := α) hP hV (bX0_spec.1)
  have hX0norm : B X0 X0 = 1 := by
    have h := cv_form (α := α) hP hV hB X0 X0
    rw [hX0, bX0_spec.2] at h
    exact (by decide : ∀ t : ZMod 3, 2 = 2 * t → t = 1) _ h
  have hX0ne : X0 ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hX0norm
    exact absurd hX0norm (by decide)
  have hxne : x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hx
    exact absurd hx (by decide)
  obtain ⟨g, hg, hgx⟩ :=
    exists_mem_e6Weyl_apply_eq (B := B) hP hV hB hα hX0ne hxne (by rw [hX0norm, hx])
  let y' : V := g.symm y
  have hgy' : g y' = y := by simp [y']
  have hy'norm : B y' y' = 1 := by
    have h := bilinForm_apply_e6Weyl (B := B) hP hV hB hα hg y' y'
    rw [hgy', hy] at h
    exact h.symm
  have hX0y' : B X0 y' = 0 := by
    have h := bilinForm_apply_e6Weyl (B := B) hP hV hB hα hg X0 y'
    rw [hgx, hgy', hxy] at h
    exact h.symm
  have hc_norm : f6 (cv hP hV y') (cv hP hV y') = 2 := by
    rw [cv_form (α := α) hP hV hB, hy'norm]
    decide
  have hc_X0 : f6 (cv hP hV y') bX0 = 0 := by
    rw [← hX0, cv_form (α := α) hP hV hB, bilinForm_symm hP hV hB y' X0, hX0y']
    decide
  have hc_mem : cv hP hV y' ∈ bPerp0 :=
    (bPerp0_spec (cv hP hV y')).mpr ⟨cv_mem_hypE6 hP hV y', hc_norm, hc_X0⟩
  obtain ⟨z1, hz1, z2, hz2, z3, hz3, -, -, -, -, -, -, hframe⟩ := bFrameCheck _ hc_mem
  obtain ⟨Z1, hZ1⟩ := exists_cv_eq (α := α) hP hV ((bPerp0_spec z1).mp hz1).1
  obtain ⟨Z2, hZ2⟩ := exists_cv_eq (α := α) hP hV ((bPerp0_spec z2).mp hz2).1
  obtain ⟨Z3, hZ3⟩ := exists_cv_eq (α := α) hP hV ((bPerp0_spec z3).mp hz3).1
  let F : Fin 5 → V := ![X0, y', Z1, Z2, Z3]
  have hFcv : ∀ k : Fin 5, cv hP hV (F k) = frameVec (cv hP hV y') z1 z2 z3 k := by
    intro k
    fin_cases k <;> simp [F, frameVec, hX0, hZ1, hZ2, hZ3]
  have hBF : ∀ i j, B (F i) (F j) = if i = j then 1 else 0 := by
    intro i j
    have h := cv_form (α := α) hP hV hB (F i) (F j)
    rw [hFcv i, hFcv j, frameGramOk_spec hframe i j] at h
    by_cases hij : i = j
    · rw [if_pos hij] at h ⊢
      exact (by decide : ∀ t : ZMod 3, 2 = 2 * t → t = 1) _ h
    · rw [if_neg hij] at h ⊢
      exact (by decide : ∀ t : ZMod 3, 0 = 2 * t → t = 0) _ h
  refine ⟨fun k => g (F k), ?_, ?_, ?_⟩
  · intro i j
    rw [bilinForm_apply_e6Weyl (B := B) hP hV hB hα hg]
    exact hBF i j
  · show g (F 0) = x
    rw [show F 0 = X0 from rfl, hgx]
  · show g (F 1) = y
    rw [show F 1 = y' from rfl, hgy']

end CFSG.StandardType.E6QTwo

end

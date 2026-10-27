module

public import CFSG.Sporadic.Schreier.Co1TernaryCode
public import Certificates.Certificate16017

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

abbrev Mat12 : Type := Matrix (Fin 12) (Fin 12) (ZMod 3)

abbrev GL12 : Type := GL (Fin 12) (ZMod 3)

@[expose] def lineMap (g : Mat12) (j : Fin 12) : Fin 12 :=
  ((List.finRange 12).find? fun i => g i j ≠ 0).getD j

@[expose] def IsMono (g : Mat12) : Prop := ∀ j i, g i j ≠ 0 ↔ i = lineMap g j

instance (g : Mat12) : Decidable (IsMono g) :=
  decidable_of_iff ((List.finRange 12).all fun j => (List.finRange 12).all fun i =>
      decide (g i j ≠ 0) == decide (i = lineMap g j)) (by
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq, decide_eq_decide]
    rfl)

theorem find?_eq_self :
    ∀ k : Fin 12, (List.finRange 12).find? (fun i => decide (i = k)) = some k :=
  Certificates.certificate16017

theorem lineMap_eq
    {g : Mat12} {j k : Fin 12} (h : ∀ i, g i j ≠ 0 ↔ i = k) : lineMap g j = k := by
  unfold lineMap
  have : (fun i => decide (g i j ≠ 0)) = fun i => decide (i = k) := by
    funext i
    exact decide_eq_decide.mpr (h i)
  rw [this, find?_eq_self]
  rfl

theorem IsMono.ne_zero {g : Mat12} (hg : IsMono g) (j : Fin 12) : g (lineMap g j) j ≠ 0 :=
  (hg j _).mpr rfl

theorem IsMono.eq_zero {g : Mat12} (hg : IsMono g) {i j : Fin 12} (h : i ≠ lineMap g j) :
    g i j = 0 := by
  by_contra h'
  exact h ((hg j i).mp h')

theorem IsMono.mul_apply {g h : Mat12} (hh : IsMono h) (i j : Fin 12) :
    (g * h) i j = g i (lineMap h j) * h (lineMap h j) j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single (lineMap h j) (fun l _ hl => ?_)
    (fun h' => absurd (Finset.mem_univ _) h')
  rw [hh.eq_zero hl, mul_zero]

theorem IsMono.mul {g h : Mat12} (hg : IsMono g) (hh : IsMono h) :
    IsMono (g * h) ∧ ∀ j, lineMap (g * h) j = lineMap g (lineMap h j) := by
  have key : ∀ i j, (g * h) i j ≠ 0 ↔ i = lineMap g (lineMap h j) := by
    intro i j
    rw [hh.mul_apply, ← hg (lineMap h j) i]
    constructor
    · intro h' h0
      rw [h0, zero_mul] at h'
      exact h' rfl
    · intro h'
      exact mul_ne_zero h' (hh.ne_zero j)
  have hL : ∀ j, lineMap (g * h) j = lineMap g (lineMap h j) := fun j => lineMap_eq (key · j)
  refine ⟨fun j i => ?_, hL⟩
  rw [hL]
  exact key i j

theorem isMono_one : IsMono (1 : Mat12) ∧ ∀ j, lineMap 1 j = j := by
  have key : ∀ i j : Fin 12, (1 : Mat12) i j ≠ 0 ↔ i = j := by
    intro i j
    rw [Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h]
  have hL : ∀ j, lineMap 1 j = j := fun j => lineMap_eq (key · j)
  refine ⟨fun j i => ?_, hL⟩
  rw [hL]
  exact key i j

theorem IsMono.eq_diagonal {g : Mat12} (hg : IsMono g) (h : ∀ j, lineMap g j = j) :
    g = Matrix.diagonal fun j => g j j := by
  ext i j
  rw [Matrix.diagonal_apply]
  split_ifs with hij
  · rw [hij]
  · exact hg.eq_zero (by rw [h]; exact hij)

@[expose] def monoEnd
    (H : Subgroup GL12) (hH : ∀ g ∈ H, IsMono (g : Mat12)) :
    H →* Function.End (Fin 12) where
  toFun g := lineMap ((g : GL12) : Mat12)
  map_one' := funext isMono_one.2
  map_mul' g h := funext ((hH g g.2).mul (hH h h.2)).2

@[expose] def monoPerm
    (H : Subgroup GL12) (hH : ∀ g ∈ H, IsMono (g : Mat12)) :
    H →* Equiv.Perm (Fin 12) :=
  (monoEnd H hH).toHomPerm

theorem monoPerm_apply
    (H : Subgroup GL12) (hH : ∀ g ∈ H, IsMono (g : Mat12)) (g : H)
    (j : Fin 12) : monoPerm H hH g j = lineMap ((g : GL12) : Mat12) j := rfl

theorem mem_T_iff_mulVec (v : Fin 12 → ZMod 3) : v ∈ T ↔ R *ᵥ v = 0 := by
  rw [mem_T_iff_orthogonal]
  constructor
  · intro h
    funext i
    rw [Pi.zero_apply]
    change (fun j => R i j) ⬝ᵥ v = 0
    rw [dotProduct_comm]
    exact h (R i) (Submodule.subset_span ⟨i, rfl⟩)
  · intro h w hw
    obtain ⟨b, rfl⟩ := (mem_T_iff w).mp hw
    rw [dotProduct_comm, ← dotProduct_mulVec, h, dotProduct_zero]

end CFSG.Sporadic.Co1Schreier

module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4Irr

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ minorJ_apply minorJ_mul_self mul_minorJ_mul_transpose_of_mem)

variable {k : Type} [Field k]

theorem mul_apply_mem {F₀ : Subfield k} {A B : Matrix (Fin 4) (Fin 4) k}
    (hA : ∀ i j, A i j ∈ F₀) (hB : ∀ i j, B i j ∈ F₀) (i j : Fin 4) : (A * B) i j ∈ F₀ := by
  rw [Matrix.mul_apply]
  exact F₀.sum_mem fun l _ => F₀.mul_mem (hA i l) (hB l j)

theorem minorJ_apply_mem (F₀ : Subfield k) (i j : Fin 4) : minorJ k i j ∈ F₀ := by
  rw [minorJ_apply]
  split_ifs
  exacts [F₀.one_mem, F₀.zero_mem]

theorem glMat_inv_eq (g : antiSp k) :
    glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) =
      minorJ k * (glMat (g : GL (Fin 4) k)).transpose * minorJ k := by
  set A := glMat (g : GL (Fin 4) k)
  have h1 : A * (minorJ k * A.transpose * minorJ k) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_minorJ_mul_transpose_of_mem g.2,
      minorJ_mul_self]
  have h2 : glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) * A = 1 := by
    change (((g : GL (Fin 4) k)⁻¹ : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) * A = 1
    exact (g : GL (Fin 4) k).inv_mul
  calc glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k)
      = glMat ((g⁻¹ : antiSp k) : GL (Fin 4) k) * (A * (minorJ k * A.transpose * minorJ k)) := by
        rw [h1, Matrix.mul_one]
    _ = minorJ k * A.transpose * minorJ k := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

@[expose] def subfieldSp (F₀ : Subfield k) : Subgroup (antiSp k) where
  carrier := {g | ∀ i j, glMat (g : GL (Fin 4) k) i j ∈ F₀}
  mul_mem' := by
    intro g h hg hh i j
    exact mul_apply_mem (A := glMat (g : GL (Fin 4) k)) (B := glMat (h : GL (Fin 4) k)) hg hh i j
  one_mem' := by
    intro i j
    change (1 : Matrix (Fin 4) (Fin 4) k) i j ∈ F₀
    rw [Matrix.one_apply]
    split_ifs
    exacts [F₀.one_mem, F₀.zero_mem]
  inv_mem' := by
    intro g hg i j
    rw [glMat_inv_eq]
    exact mul_apply_mem (mul_apply_mem (minorJ_apply_mem F₀) (fun a b => hg b a))
      (minorJ_apply_mem F₀) i j

@[expose] def transvSet (G₀ : Subgroup (antiSp k)) : Set (antiSp k) :=
  {d | d ∈ G₀ ∧ IsTransvection d}

end CFSG.Quasithin.Ch3E213M

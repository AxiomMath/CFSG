module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat minorJ uElt uMat_zero antiSp_ext uElt_mul uElt_inv antiUnipotentCenter)

variable {k : Type} [Field k]

@[expose] def natAct (g : antiSp k) (v : Fin 4 → k) : Fin 4 → k :=
  (glMat (g : GL (Fin 4) k)).mulVec v

theorem natAct_one (v : Fin 4 → k) : natAct (1 : antiSp k) v = v := by
  simp [natAct]

theorem natAct_mul (g h : antiSp k) (v : Fin 4 → k) :
    natAct (g * h) v = natAct g (natAct h v) := by
  simp [natAct, Matrix.mulVec_mulVec]

@[expose] def natLin (g : antiSp k) : (Fin 4 → k) →ₗ[k] (Fin 4 → k) :=
  Matrix.toLin' (glMat (g : GL (Fin 4) k))

@[expose] def IsIrreducibleSp4 (X : Subgroup (antiSp k)) : Prop :=
  ∀ W : Submodule k (Fin 4 → k), (∀ g ∈ X, ∀ w ∈ W, natAct g w ∈ W) → W = ⊥ ∨ W = ⊤

@[expose] def commSpace (g : antiSp k) : Submodule k (Fin 4 → k) :=
  LinearMap.range (Matrix.toLin' (glMat (g : GL (Fin 4) k) - 1))

@[expose] def IsTransvection (g : antiSp k) : Prop :=
  g ≠ 1 ∧ Module.finrank k (commSpace g) = 1

@[expose] def spBil : LinearMap.BilinForm k (Fin 4 → k) :=
  Matrix.toBilin' (minorJ k)

section CharTwo

variable [CharP k 2]

@[expose] def zLine (α β : k) : Subgroup (antiSp k) where
  carrier := {g | ∃ t : k, g = uElt 0 (t * β) (t * α) 0}
  mul_mem' := by
    rintro _ _ ⟨t, rfl⟩ ⟨s, rfl⟩
    exact ⟨t + s, by rw [uElt_mul]; congr 1 <;> ring⟩
  one_mem' := ⟨0, by rw [zero_mul, zero_mul]; exact antiSp_ext uMat_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, by rw [uElt_inv]; congr 1; ring⟩

@[expose] def SpansCenter (W : Subgroup (antiSp k)) : Prop :=
  ∀ α β : k, (α ≠ 0 ∨ β ≠ 0) → ¬ W ≤ zLine α β

end CharTwo

@[expose] def IsOppStd (g : antiSp k) : Prop :=
  glMat (g : GL (Fin 4) k) 3 0 ≠ 0 ∧
    glMat (g : GL (Fin 4) k) 2 0 * glMat (g : GL (Fin 4) k) 3 1 -
      glMat (g : GL (Fin 4) k) 2 1 * glMat (g : GL (Fin 4) k) 3 0 ≠ 0

@[expose] def IrrStatement : Prop :=
  ∀ (k : Type) [Field k] [CharP k 2] (W : Subgroup (antiSp k)) (g : antiSp k),
    W ≤ antiUnipotentCenter k → SpansCenter W → IsOppStd g →
    IsIrreducibleSp4 (W ⊔ W.map (MulAut.conj g).toMonoidHom)

end CFSG.Quasithin.Ch3E213M

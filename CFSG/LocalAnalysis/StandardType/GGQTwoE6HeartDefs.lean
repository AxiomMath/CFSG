module

public import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Certificates.Data.E6Heart

public section

open Matrix

namespace CFSG.StandardType.E6Heart

abbrev C : Matrix (Fin 6) (Fin 6) ℤ := CartanMatrix.E 6

@[expose] def rad : Fin 6 → ZMod 3 := ![1, 0, 2, 0, 1, 2]

abbrev H : Type := (Fin 6 → ZMod 3) ⧸ Submodule.span (ZMod 3) {rad}

@[expose] def toVec (a : List ℤ) : Fin 6 → ℤ := fun i => a.getD i 0

@[expose] def roots : Finset (Fin 6 → ℤ) := (Certificates.E6Heart.roots.map toVec).toFinset

@[expose] def ipair (a b : Fin 6 → ℤ) : ℤ := ∑ i, ∑ j, a i * C i j * b j

@[expose] def pair (a : Fin 6 → ℤ) (y : Fin 6 → ZMod 3) : ZMod 3 :=
  ∑ i, ∑ j, (a i : ZMod 3) * (C i j : ZMod 3) * y j

@[expose] def Q (y : Fin 6 → ZMod 3) : ZMod 3 := ∑ i, ∑ j, y i * (C i j : ZMod 3) * y j

@[expose] def pairLin (a : Fin 6 → ℤ) : (Fin 6 → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun := pair a
  map_add' x y := by simp [pair, Finset.sum_add_distrib, mul_add]
  map_smul' c x := by simp [pair, Finset.mul_sum, mul_left_comm]

private theorem ggE6d_C_symm (i j : Fin 6) : C i j = C j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem pairLin_rad (a : Fin 6 → ℤ) : pairLin a rad = 0 := by
  have hC : ∀ i : Fin 6, (∑ j, (C i j : ZMod 3) * rad j) = 0 := by
    intro i; fin_cases i <;> decide
  change pair a rad = 0
  rw [pair]
  apply Finset.sum_eq_zero
  intro i _
  rw [show (∑ j, (a i : ZMod 3) * (C i j : ZMod 3) * rad j) =
      (a i) * (∑ j, (C i j : ZMod 3) * rad j) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _; ring]
  rw [hC i, mul_zero]

@[expose] def alpha (a : Fin 6 → ℤ) : H →ₗ[ZMod 3] ZMod 3 :=
  Submodule.liftQ _ (pairLin a) (by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact pairLin_rad a)

private theorem ggE6d_Q_dot (w : Fin 6 → ZMod 3) :
    Q w = dotProduct w ((C.map (fun z => (z : ZMod 3))) *ᵥ w) := by
  simp only [Q, dotProduct, mulVec, Matrix.map_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem Q_add_rad (y : Fin 6 → ZMod 3) (m : ZMod 3) : Q (y + m • rad) = Q y := by
  have hC : ∀ i : Fin 6, (∑ j, (C i j : ZMod 3) * rad j) = 0 := by
    intro i; fin_cases i <;> decide
  have hrad : (C.map (fun z => (z : ZMod 3))) *ᵥ rad = 0 := by
    funext i
    simp only [mulVec, Matrix.map_apply, Pi.zero_apply]
    exact hC i
  have hsym : (C.map (fun z => (z : ZMod 3)))ᵀ = C.map (fun z => (z : ZMod 3)) := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply]
    rw [ggE6d_C_symm]
  rw [ggE6d_Q_dot, ggE6d_Q_dot, mulVec_add, mulVec_smul, hrad, smul_zero, add_zero]
  rw [add_dotProduct, smul_dotProduct]
  have hzero : dotProduct rad ((C.map (fun z => (z : ZMod 3))) *ᵥ y) = 0 := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, hrad]
    simp [dotProduct]
  rw [hzero, smul_zero, add_zero]

@[expose] def Qh : H → ZMod 3 :=
  Quotient.lift (s := Submodule.quotientRel _) Q (fun a b hab => by
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp ((Submodule.quotientRel_def _).mp hab)
    have h : a = b + m • rad := by rw [hm]; abel
    rw [h, Q_add_rad])

@[expose] def Phi (y : H) : Finset (Fin 6 → ℤ) := roots.filter fun a => alpha a y = 0

@[expose] def graph (y : H) : SimpleGraph (Phi y) :=
  SimpleGraph.fromRel fun a b => ipair a.1 b.1 ≠ 0

@[expose] noncomputable def compSize (y : H) (c : (graph y).ConnectedComponent) : ℕ :=
  Nat.card c.supp

@[expose] def compKernel (y : H) (c : (graph y).ConnectedComponent) : Set H :=
  {t | ∀ a : Phi y, a ∈ c.supp → alpha a.1 t = 0}

end CFSG.StandardType.E6Heart

end

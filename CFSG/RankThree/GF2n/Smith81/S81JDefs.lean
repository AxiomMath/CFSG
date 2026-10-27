module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.GF2n.Smith81.S81A5Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.S81J

open CFSG.RankThree.GF2n.Smith81.A5Cube Matrix

@[expose] def dg {K : Type*} [Field K] (d : Fin 6 → Kˣ) : GL (Fin 6) K where
  val := Matrix.diagonal fun i => (d i : K)
  inv := Matrix.diagonal fun i => (((d i)⁻¹ : Kˣ) : K)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

@[expose] def pm (K : Type*) [Field K] : Equiv.Perm (Fin 6) →* GL (Fin 6) K :=
  (Matrix.permMatrixHom (n := Fin 6) (R := K)).toHomUnits

@[expose] def cOn {K : Type*} [Field K] (a b : Fin 6) (c : Kˣ) : Fin 6 → Kˣ :=
  fun i => if i = a then c else if i = b then c⁻¹ else 1

@[expose] def Wc (K : Type*) [Field K] (I : Finset (Fin 6)) : Submodule K (Fin 6 → K) where
  carrier := {v | ∀ i, i ∉ I → v i = 0}
  add_mem' := fun ha hb i hi => by simp [ha i hi, hb i hi]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c _ hv i hi => by simp [hv i hi]

@[expose] def I0 : Finset (Fin 6) := {0, 1, 2}

theorem mem_Wc {K : Type*} [Field K] {I : Finset (Fin 6)} {v : Fin 6 → K} :
    v ∈ Wc K I ↔ ∀ i, i ∉ I → v i = 0 := Iff.rfl

end CFSG.RankThree.GF2n.Smith81.S81J

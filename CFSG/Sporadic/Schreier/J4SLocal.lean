module

public import CFSG.Sporadic.J4.Action
public import CFSG.Sporadic.Schreier.J4SData
public import CFSG.Sporadic.HS.SmallF2Spec

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ

@[expose] def regs : ℕ → J := runProg (initRegs a b) typeIIProg

@[expose] def x : J := regs 1

@[expose] def y : J := regs 2

@[expose] def t : J := regs 3

@[expose] def d : J := (y * x) ^ 4 * y⁻¹ * x

@[expose] def z : J := (y * d⁻¹ * t * d) ^ 3

@[expose] def c (j : Fin 11) : J := signedWord x y (normalConjugators j)

@[expose] def u (j : Fin 11) : J := (c j)⁻¹ * z * c j

@[expose] def η (i : ℕ) : J := (List.ofFn fun j : Fin 11 => if i.testBit j then u j else 1).prod

@[expose] def N : Subgroup J := Subgroup.closure (Set.range u)

@[expose] def K : Subgroup J := Subgroup.closure {x, y}

@[expose] def H : Subgroup J := Subgroup.closure {x, y, z}

@[expose] def v : Row := toRow (CFSG.Sporadic.SmallF2.toVecD 112 rootBits)

theorem x_mem_K : x ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)

theorem y_mem_K : y ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem x_mem_H : x ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)

theorem y_mem_H : y ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem z_mem_H : z ∈ H :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem K_le_H : K ≤ H := by
  rw [K, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact x_mem_H
  · exact y_mem_H

theorem signedWord_mem_K (w : List ℤ) : signedWord x y w ∈ K :=
  signedWord_mem K x_mem_K y_mem_K w

theorem c_mem_K (j : Fin 11) : c j ∈ K := signedWord_mem_K _

theorem u_mem_H (j : Fin 11) : u j ∈ H :=
  H.mul_mem (H.mul_mem (H.inv_mem (K_le_H (c_mem_K j))) z_mem_H) (K_le_H (c_mem_K j))

theorem u_mem_N (j : Fin 11) : u j ∈ N := Subgroup.subset_closure ⟨j, rfl⟩

theorem N_le_H : N ≤ H := by
  rw [N, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact u_mem_H j

theorem η_mem_N (i : ℕ) : η i ∈ N := by
  unfold η
  refine N.list_prod_mem fun g hg => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  split_ifs
  · exact u_mem_N j
  · exact N.one_mem

theorem u_zero : u 0 = z := by
  simp [u, c, normalConjugators, signedWord]

theorem z_mem_N : z ∈ N := u_zero ▸ u_mem_N 0

end CFSG.Sporadic.J4Schreier

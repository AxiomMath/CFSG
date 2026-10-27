module

public import Certificates.Data.A8Nbr476

public section

namespace CFSG.StandardType.A8Coord

open Certificates.A8Nbr476 Matrix

@[expose] def a8PermMat (σ : Equiv.Perm (Fin 4)) : M4 :=
  Matrix.of fun i j => if σ i = j then 1 else 0

@[expose] def a8MonK3 (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) : M3 :=
  Matrix.of fun i j => if π i = j then (2 : ZMod 7) ^ (k i).val else 0

@[expose] def a8MonK (π : Equiv.Perm (Fin 3)) (k : Fin 3 → ZMod 3) : M4 :=
  blk (a8MonK3 π k)

@[expose] def a8P (p₁ p₂ u₀ u₁ u₂ : ZMod 7) : M4 :=
  !![p₁, p₂, p₂, p₂; u₀, u₁, u₂, u₂; u₀, u₂, u₁, u₂; u₀, u₂, u₂, u₁]

theorem genK_eq_a8MonK :
    genK 0 = a8MonK (Equiv.swap 0 1) 0 ∧ genK 1 = a8MonK (Equiv.swap 1 2) 0 ∧
      genK 2 = a8MonK 1 ![1, 0, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end CFSG.StandardType.A8Coord

end

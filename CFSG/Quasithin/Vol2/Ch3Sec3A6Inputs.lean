module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Defs

public section

namespace CFSG.Quasithin.H13.A6Coc

abbrev Vec4 : Type := Fin 4 → ZMod 2

@[expose] def crdM : Matrix (Fin 4) (Fin 6) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 1; 1, 1, 0, 0, 0, 0; 1, 1, 1, 0, 0, 1; 1, 1, 1, 1, 0, 0]

@[expose] def secM : Matrix (Fin 6) (Fin 4) (ZMod 2) :=
  !![1, 0, 0, 0; 1, 1, 0, 0; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1; 0, 0, 0, 0]

@[expose] def crd (x : Fin 6 → ZMod 2) : Vec4 := crdM.mulVec x

@[expose] def sec (v : Vec4) : Fin 6 → ZMod 2 := secM.mulVec v

@[expose] def act (σ : Equiv.Perm (Fin 6)) (v : Vec4) : Vec4 :=
  crd fun i => sec v (σ⁻¹ i)

@[expose] def aP : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def bP : Equiv.Perm (Fin 6) :=
  Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def fixCount (σ : Equiv.Perm (Fin 6)) : ℕ :=
  (Finset.univ.filter fun v : Vec4 => act σ v = v).card

end CFSG.Quasithin.H13.A6Coc

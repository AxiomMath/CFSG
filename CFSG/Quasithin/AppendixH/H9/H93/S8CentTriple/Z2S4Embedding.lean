module

public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.ASVolI.ChH

open Equiv

def stdTripleTransposition : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5

def twoSubsetIndex : Fin 4 → Fin 4 → Fin 8 :=
  ![![0, 0, 2, 4], ![0, 0, 5, 3], ![2, 5, 0, 1], ![4, 3, 1, 0]]

def twoSubsetEnds : Fin 8 → Fin 4 × Fin 4 :=
  ![(0, 1), (2, 3), (0, 2), (1, 3), (0, 3), (1, 2), (0, 0), (0, 0)]

def s4ActOnTwoSubsets (σ : Perm (Fin 4)) (i : Fin 8) : Fin 8 :=
  if i.val < 6 then twoSubsetIndex (σ (twoSubsetEnds i).1) (σ (twoSubsetEnds i).2) else i

private theorem s4ActOnTwoSubsets_one (i : Fin 8) : s4ActOnTwoSubsets 1 i = i := by
  revert i; decide

private theorem s4ActOnTwoSubsets_mul (σ τ : Perm (Fin 4)) (i : Fin 8) :
    s4ActOnTwoSubsets (σ * τ) i = s4ActOnTwoSubsets σ (s4ActOnTwoSubsets τ i) := by
  revert σ τ i; decide +kernel

def s4OnTwoSubsets : Perm (Fin 4) →* Perm (Fin 8) where
  toFun σ :=
    { toFun := s4ActOnTwoSubsets σ
      invFun := s4ActOnTwoSubsets σ⁻¹
      left_inv := fun i => by rw [← s4ActOnTwoSubsets_mul, inv_mul_cancel, s4ActOnTwoSubsets_one]
      right_inv := fun i => by rw [← s4ActOnTwoSubsets_mul, mul_inv_cancel, s4ActOnTwoSubsets_one] }
  map_one' := Equiv.ext s4ActOnTwoSubsets_one
  map_mul' σ τ := Equiv.ext (s4ActOnTwoSubsets_mul σ τ)

def stdQuadTransposition : Perm (Fin 8) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7

def quadTranspositionHom : Multiplicative (ZMod 2) →* Perm (Fin 8) :=
  MonoidHom.mk' (fun e => if e = 1 then 1 else stdQuadTransposition) (by decide)

private theorem quadTranspositionHom_comm (e : Multiplicative (ZMod 2)) (σ : Perm (Fin 4)) :
    quadTranspositionHom e * s4OnTwoSubsets σ = s4OnTwoSubsets σ * quadTranspositionHom e := by
  revert e σ; decide +kernel

def z2S4Embed : Multiplicative (ZMod 2) × Perm (Fin 4) →* Perm (Fin 8) :=
  quadTranspositionHom.noncommCoprod s4OnTwoSubsets quadTranspositionHom_comm

theorem z2S4Embed_injective : Function.Injective z2S4Embed := by
  rw [injective_iff_map_eq_one]; decide +kernel

theorem sign_z2S4Embed (x : Multiplicative (ZMod 2) × Perm (Fin 4)) :
    Perm.sign (z2S4Embed x) = 1 := by
  revert x; decide +kernel

theorem z2S4Embed_mul_stdTripleTransposition (x : Multiplicative (ZMod 2) × Perm (Fin 4)) :
    z2S4Embed x * stdTripleTransposition = stdTripleTransposition * z2S4Embed x := by
  revert x; decide +kernel

theorem cycleType_stdTripleTransposition : stdTripleTransposition.cycleType = {2, 2, 2} := by
  have h1 : (swap (0 : Fin 8) 1 * swap 2 3).cycleType = {2, 2} :=
    Perm.cycleType_swap_mul_swap_of_nodup (by decide)
  have h2 : (swap (4 : Fin 8) 5).cycleType = {2} := by
    rw [(Perm.isCycle_swap (by decide : (4 : Fin 8) ≠ 5)).cycleType,
      Perm.card_support_swap (by decide : (4 : Fin 8) ≠ 5)]
  have hd : Perm.Disjoint (swap (0 : Fin 8) 1 * swap 2 3) (swap 4 5) := by
    intro x; revert x; decide
  show (swap (0 : Fin 8) 1 * swap 2 3 * swap 4 5).cycleType = {2, 2, 2}
  rw [hd.cycleType_mul, h1, h2]
  rfl

end CFSG.ASVolI.ChH

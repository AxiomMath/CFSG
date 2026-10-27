module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

abbrev P8 := Equiv.Perm (Fin 8)
@[expose] def m₁ : P8 := List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5]
@[expose] def m₂ : P8 := List.formPerm [0, 1, 2] * List.formPerm [3, 5, 4]
@[expose] def τ₀ : P8 := Equiv.swap 6 7
@[expose] def Eo : Subgroup P8 := Subgroup.closure {m₁, m₂}
@[expose] def A8s : Subgroup P8 := alternatingGroup (Fin 8)
@[expose] def A6tau : Subgroup P8 :=
  (commutator ↥(Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s)).map (Subgroup.centralizer ({τ₀} : Set P8) ⊓ A8s).subtype
@[expose] def U₁ : Subgroup P8 := Subgroup.closure {(Equiv.swap 0 1) * (Equiv.swap 2 6), (Equiv.swap 0 2) * (Equiv.swap 1 6),
  (Equiv.swap 3 4) * (Equiv.swap 5 7), (Equiv.swap 3 5) * (Equiv.swap 4 7)}
@[expose] def U₂ : Subgroup P8 := Subgroup.closure {(Equiv.swap 0 1) * (Equiv.swap 2 7), (Equiv.swap 0 2) * (Equiv.swap 1 7),
  (Equiv.swap 3 4) * (Equiv.swap 5 6), (Equiv.swap 3 5) * (Equiv.swap 4 6)}

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

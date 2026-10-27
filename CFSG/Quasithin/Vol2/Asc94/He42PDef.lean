module

public import Mathlib

public section

namespace CFSG.Quasithin.A94.He42PD

open Equiv Subgroup

variable {Δ : Type*} [Group Δ]

structure PData (L K A J : Subgroup Δ) (ψ : ↥L →* Perm (Fin 5)) : Prop where
  KL : K ≤ L
  AJ : A ≤ J
  JK : J ≤ K
  A_normal : ∀ l ∈ L, ∀ a ∈ A, l * a * l⁻¹ ∈ A
  ker : ψ.ker = A.subgroupOf L
  range : ψ.range = alternatingGroup (Fin 5)
  stab : ∀ k : ↥L, ψ k 0 = 0 ↔ (k : Δ) ∈ K
  Jcard : Nat.card ((J.subgroupOf L).map ψ) = 4

end CFSG.Quasithin.A94.He42PD

module

public import CFSG.Quasithin.H13.A6F91General
public import CFSG.Quasithin.H13.A6Setting4

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def RedList : List (Perm (Fin 6)) :=
  [swap 3 4 * swap 4 5, swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5), swap 1 2 * swap 4 5]

@[expose] def RedWit (σ : Perm (Fin 6)) : Prop :=
  ∃ τ ∈ RedList, (σ * τ * σ⁻¹ * τ⁻¹) ^ 4 ≠ 1

instance (σ : Perm (Fin 6)) : Decidable (RedWit σ) := by unfold RedWit; infer_instance

variable {G : Type} [Group G]

namespace Setting4

variable [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

end Setting4

end CFSG.Quasithin.H13.A6

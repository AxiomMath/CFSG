module

public import CFSG.Quasithin.Recognition.M12AscL2

public section

namespace CFSG.Quasithin

open Subgroup Equiv

open CFSG.GH74.M12 (Asc03Hyp)

variable {G : Type*} [Group G] {z : G}

@[expose] def actD (σ : Perm (Fin 6)) : Perm (Fin 6) × Perm (Fin 6) :=
  (σ * x6 * σ⁻¹, σ * x16 * σ⁻¹)

@[expose] def actE (σ : Perm (Fin 6)) : Perm (Fin 6) × Perm (Fin 6) :=
  (σ * ax6 * σ⁻¹, σ * ax16 * σ⁻¹)

@[expose] def W1 : List (Perm (Fin 6)) :=
  [evalWord swapGen [], evalWord swapGen [1, 4], evalWord swapGen [1, 2, 1, 0, 3, 2, 1, 4, 3, 2],
   evalWord swapGen [2, 1, 0, 3, 2, 1, 4, 3, 2, 1]]

@[expose] def W2 : List (Perm (Fin 6)) :=
  [evalWord swapGen [2, 1, 3, 2], evalWord swapGen [1, 2, 1, 4, 3, 2],
   evalWord swapGen [2, 1, 0, 3, 4, 3], evalWord swapGen [1, 2, 1, 0, 3, 4]]

@[expose] def InKP (p : Perm (Fin 6) × Perm (Fin 6)) : Prop :=
  (∃ σ ∈ W1, actD σ = p) ∨ (∃ σ ∈ W2, actE σ = p)

instance : DecidablePred InKP := fun p => by unfold InKP; infer_instance

end CFSG.Quasithin

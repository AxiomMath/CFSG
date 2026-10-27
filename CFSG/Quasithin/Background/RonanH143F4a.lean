module

public import CFSG.Quasithin.Background.RonanH143Data

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

@[expose] def alt5Gen (b : Bool) : Equiv.Perm (Fin 5) := if b then sig1 else siga2

@[expose] def evalWord (w : List Bool) : Equiv.Perm (Fin 5) := (w.map alt5Gen).prod

@[expose] def alt5Words : List (List Bool) :=
  [[], [true], [false], [true, true], [true, false], [false, true], [true, true, true],
   [true, true, false], [true, false, true], [false, true, true], [false, true, false],
   [true, true, true, true], [true, true, true, false], [true, true, false, true],
   [true, false, true, true], [true, false, true, false], [false, true, true, true],
   [false, true, true, false], [false, true, false, true], [true, true, true, true, false],
   [true, true, true, false, true], [true, true, false, true, true],
   [true, true, false, true, false], [true, false, true, true, true],
   [true, false, true, true, false], [true, false, true, false, true],
   [false, true, true, true, true], [false, true, true, false, true],
   [false, true, false, true, true], [false, true, false, true, false],
   [true, true, true, true, false, true], [true, true, true, false, true, true],
   [true, true, true, false, true, false], [true, true, false, true, true, true],
   [true, true, false, true, false, true], [true, false, true, true, true, true],
   [true, false, true, true, false, true], [true, false, true, false, true, true],
   [true, false, true, false, true, false], [false, true, true, true, true, false],
   [false, true, true, false, true, false], [false, true, false, true, true, true],
   [false, true, false, true, true, false], [false, true, false, true, false, true],
   [true, true, true, true, false, true, true], [true, true, true, true, false, true, false],
   [true, true, false, true, true, true, true], [true, true, false, true, false, true, false],
   [true, false, true, true, true, true, false], [true, false, true, false, true, true, false],
   [false, true, true, true, true, false, true], [false, true, true, false, true, false, true],
   [false, true, false, true, true, true, true], [false, true, false, true, false, true, true],
   [true, false, true, true, true, true, false, true],
   [false, true, true, true, true, false, true, false],
   [false, true, true, false, true, false, true, false],
   [false, true, false, true, true, true, true, false],
   [false, true, false, true, false, true, true, false],
   [true, false, true, true, true, true, false, true, false]]

theorem alt5_covers :
    ∀ τ : Equiv.Perm (Fin 5), Equiv.Perm.sign τ = 1 → ∃ w ∈ alt5Words, evalWord w = τ := by
  decide +kernel

theorem evalWord_mem (w : List Bool) :
    evalWord w ∈ Subgroup.closure ({sig1, siga2} : Set (Equiv.Perm (Fin 5))) := by
  unfold evalWord
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure (by cases b <;> simp [alt5Gen])

theorem alt5_le_closure :
    alternatingGroup (Fin 5) ≤ Subgroup.closure ({sig1, siga2} : Set (Equiv.Perm (Fin 5))) := by
  intro τ hτ
  obtain ⟨w, -, rfl⟩ := alt5_covers τ (Equiv.Perm.mem_alternatingGroup.mp hτ)
  exact evalWord_mem w

end CFSG.Quasithin.RonanH143

module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModS5Base

public section

namespace CFSG.Quasithin.F53Mod

open Equiv

structure CEMod (M : Model 5) : Prop where
  nt : ∃ w : M.W, w ≠ 1
  fix : fixW M ⊤ = ⊥
  gen : ∀ U : Subgroup M.W, IsInvSub M ⊤ U → fixW M S5Syl ≤ U → U = ⊤
  red : ¬ (Nonempty (M.Iso orth) ∨ Nonempty (M.Iso nat))
  big : ∀ d ∈ alternatingGroup (Fin 5), d ≠ 1 → (d ^ 2 = 1 ∨ d ^ 3 = 1) → 8 < idx M d
  swap4 : ∀ t : Perm (Fin 5), t.IsSwap → 4 ≤ idx M t
  small : ∃ t : Perm (Fin 5), t.IsSwap ∧ idx M t ≤ 4

@[expose] def S4pt : Subgroup (Perm (Fin 5)) := MulAction.stabilizer (Perm (Fin 5)) (4 : Fin 5)

structure ShapeMod1 (M : Model 5) : Prop where
  ext : ∃ (U : Subgroup M.W) (hU : IsInvSub M ⊤ U), Nonempty ((M.restrict U hU).Iso orth) ∧
    Nonempty ((M.quot U hU).Iso orth)
  card : Nat.card M.W = 2 ^ 8
  fix_le : ∀ P : Subgroup (Perm (Fin 5)), Nat.card P = 8 → Nat.card (fixW M P) ≤ 4
  swap_eq : ∀ t : Perm (Fin 5), t.IsSwap → idx M t = 4

structure ShapeMod2 (M : Model 5) : Prop where
  fix_S4 : fixW M S5Syl = fixW M S4pt
  index_That : ∀ g : Perm (Fin 5), 16 ≤ (fixW M (S5That.map (MulAut.conj g).toMonoidHom)).index

end CFSG.Quasithin.F53Mod

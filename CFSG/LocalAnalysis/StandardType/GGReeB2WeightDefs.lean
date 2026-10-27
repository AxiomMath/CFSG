module

public import CFSG.LocalAnalysis.StandardType.GGReeB2CondCDefs

public section

namespace CFSG.StandardType.ReeB2Fixed

@[expose] def wtSet (m : ℕ) (J : Finset (Fin (2 * m + 1))) : Set (ZMod (2 ^ (2 * m + 1) - 1)) :=
  {x | ∃ y ∈ Lam (2 * m + 1) J, x = (1 + 2 ^ m) * y}

@[expose] def hw (m : ℕ) (J : Finset (Fin (2 * m + 1))) : ZMod (2 ^ (2 * m + 1) - 1) :=
  (1 + 2 ^ m) * S (2 * m + 1) J

@[expose] def OnLines {α : Type*} [Ring α] (x y : α) : Prop := x = 0 ∨ y = 0 ∨ x = y ∨ x = -y

@[expose] def sa (m : ℕ) (x : ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1)) :
    ZMod (2 ^ (2 * m + 1) - 1) × ZMod (2 ^ (2 * m + 1) - 1) :=
  (2 ^ m * (x.2 - x.1), 2 ^ m * (x.1 + x.2))

@[expose] def CondH (m : ℕ) : Prop :=
  ∀ I J : Finset (Fin (2 * m + 1)), Admissible (2 * m + 1) I J →
    ∃ κ ∈ wtSet m I, ∀ I' J' : Finset (Fin (2 * m + 1)),
      (hw m I', hw m J') = sa m (κ, hw m J) → ¬ Admissible (2 * m + 1) I' J'

end CFSG.StandardType.ReeB2Fixed

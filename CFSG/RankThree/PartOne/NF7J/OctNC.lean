module

public import Aesop.BuiltinRules
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

namespace CFSG.RankThree.PartOne.NF7J

@[expose] def OctNC (i j : Fin 8) : Prop := j - i = 3 ∨ j - i = 4 ∨ j - i = 5

instance (i j : Fin 8) : Decidable (OctNC i j) := by unfold OctNC; infer_instance

theorem octNC_c6 : ∀ x y : Fin 8, (x.val + y.val) % 2 = 1 →
    (OctNC x y ∨ OctNC x (y + 4)) ∧ ¬ (OctNC x y ∧ OctNC x (y + 4)) := by decide

theorem octNC_c7 : ∀ x y z : Fin 8, OctNC x y → y ≠ x + 4 → z ≠ x → z ≠ y → ¬ OctNC z x → ¬ OctNC z y →
    (y = x + 3 ∧ (z = x + 1 ∨ z = x + 2)) ∨ (x = y + 3 ∧ (z = y + 1 ∨ z = y + 2)) := by decide

end CFSG.RankThree.PartOne.NF7J

module

public import CFSG.Blueprint.ChevalleyRootsInputs

public section

namespace CFSG.StandardType.F4TwoNonToral

open CFSG.Blueprint.Chevalley

local instance : NeZero Tag.F4.rank := ⟨by decide⟩

@[expose] def dotRoot (α : Fin Tag.F4.rank → ℤ) (y : Fin Tag.F4.rank → ZMod 3) : ZMod 3 :=
  ∑ i, (α i : ZMod 3) * y i

private theorem exists_root_trivial_on_both (y : Fin Tag.F4.rank → ZMod 3) (hy : y ≠ 0)
    (hne : ((rootFinset .F4).filter fun α => dotRoot α y = 0).card ≠ 12)
    (z : Fin Tag.F4.rank → ZMod 3) :
    ∃ α ∈ rootFinset .F4, dotRoot α y = 0 ∧ dotRoot α z = 0 := by
  revert y hne z
  decide +kernel

theorem f4_card_trivial_eq_twelve (y z : Fin Tag.F4.rank → ZMod 3) (hy : y ≠ 0)
    (hno : ∀ α ∈ rootFinset .F4, ¬ (dotRoot α y = 0 ∧ dotRoot α z = 0)) :
    ((rootFinset .F4).filter fun α => dotRoot α y = 0).card = 12 := by
  by_contra hne
  obtain ⟨α, hα, h1, h2⟩ := exists_root_trivial_on_both y hy hne z
  exact hno α hα ⟨h1, h2⟩

end CFSG.StandardType.F4TwoNonToral

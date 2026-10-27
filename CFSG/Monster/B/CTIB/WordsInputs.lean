module

public import Certificates.Data.Kernel.BabyMonster.CTIB.CentWords
public import CFSG.Monster.B.CTIB.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix

section Word

variable {α : Type*} (L : α → Sbp) (T : α → Array ℕ) (P : α → Prop)
  (hL : ∀ a, P a → (L a).unop ∈ Jbar)
  (hT : ∀ a, P a → ∀ i < 22, (L a)⁻¹ * es i * L a = qS ((T a).getD i 0))

end Word

@[expose] def centLettersOK : Bool :=
  (List.range 45).all fun t => (centWordsL.getD t []).all fun l =>
    l == 1 || l == -1 || l == 2 || l == -2

end CFSG.Monster.B.CTIB

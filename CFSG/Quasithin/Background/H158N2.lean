module

public import CFSG.Quasithin.Background.B4ModelsSporadic

public section

namespace CFSG.Quasithin.H158N

open CFSG.Quasithin CFSG.Monster.Code

theorem mem_golay_iff' (m : G6.PermMod 24) : m ∈ golayC ↔ Multiplicative.toAdd m ∈ C := Iff.rfl

theorem permAct_mem_golay_iff {g : Equiv.Perm (Fin 24)} (hg : g ∈ CFSG.Monster.Code.AutPerm)
    (c : G6.PermMod 24) : G6.permAct 24 g c ∈ golayC ↔ c ∈ golayC := by
  have hinv := (mem_AutPerm_iff.1 (inv_mem hg) (Multiplicative.toAdd c))
  have e : Multiplicative.toAdd (G6.permAct 24 g c) = Multiplicative.toAdd c ∘ ⇑g⁻¹ := by
    funext i
    rfl
  rw [mem_golay_iff', mem_golay_iff', e]
  exact hinv.symm

end CFSG.Quasithin.H158N

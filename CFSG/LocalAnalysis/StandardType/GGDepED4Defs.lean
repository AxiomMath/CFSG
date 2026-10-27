module

public import CFSG.LocalAnalysis.StandardType.GGDepEDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGDepED4In (c : Fin 6) : Prop := c ≠ 0 ∧ c ≠ 5

@[expose] def GGDepED4Leaf (c : Fin 6) : Prop := c = 1 ∨ c = 2 ∨ c = 4

@[expose] def GGDepED4Pairs1 (c0 : Fin 6) (ha αa : GGDepAE 3 7) : Prop :=
  ∀ c : Fin 6, GGDepED4In c →
    ggDepAdot αa (ggDepEh 3 c) = (if c = c0 then (-1 : ZMod 3) else 0) ∧
      ggDepAdot (ggDepEα 3 c) ha = (if c = c0 then (-1 : ZMod 3) else 0)

@[expose] def GGDepED4Cells1 : Prop :=
  ∀ c0 : Fin 6, GGDepED4Leaf c0 → ∀ ha αa : GGDepAE 3 7, GGDepED4Pairs1 c0 ha αa →
    ggDepAdot αa ha = 2 → ggDepAdot αa (ggDepEx 3) ≠ 0 →
      ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin 6 =>
          ggDepARefl (ggDepEh 3 i) (ggDepEα 3 i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g

end CFSG.StandardType

end

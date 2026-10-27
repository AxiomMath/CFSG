module

public import CFSG.RankThree.Co2.SylFacts

public section

namespace CFSG.RankThree.Co2

@[expose] def letters21 : Array (List ℕ) :=
  #[[21], [22], [23], [24], [25], [26], [27], [28], [29], [30], [31], [32], [33], [34], [35], [36],
    [37], [38], [39], [40], [41]]

@[expose] noncomputable def Cm : Submonoid (Matrix (Fin 22) (Fin 22) (ZMod 2)) := matGrp letters21

@[expose] def CrConj (a b : Matrix (Fin 22) (Fin 22) (ZMod 2)) : Prop := ∃ g ∈ Cm, g * a = b * g

end CFSG.RankThree.Co2

end

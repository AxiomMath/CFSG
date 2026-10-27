module

public import CFSG.LieType.Ree.G2PrimeFieldWords

public section

namespace CFSG.Walter.Ree.Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

@[expose] def g2TWord : List (ℕ × ℤ) :=
  g2WeylWordInv ⟨0, by decide⟩ ++ g2WeylWordInv ⟨0, by decide⟩ ++ g2WeylWordInv ⟨1, by decide⟩ ++
    g2WeylWordInv ⟨1, by decide⟩

theorem g2Check_fusion_n :
    constCheck G2.tag 3 (g2UWord 0 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 1 ++ g2UWord 2 ++ g2TWord)
      (g2LongWord ++ (g2UWord 0 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 1 ++ g2UWord 2)) = true := by
  decide +kernel

theorem g2Check_fusion_tn :
    constCheck G2.tag 3 (g2UWord 2 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 0 ++ g2TWord)
      (g2TWord ++ g2LongWord ++ (g2UWord 2 ++ g2UWord 1 ++ g2LongWord ++ g2UWord 0)) = true := by
  decide +kernel

end CFSG.Walter.Ree.Model

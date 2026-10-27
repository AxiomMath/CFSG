module

public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofU4
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec21.Item221ResProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem item233ZRootGen_of (h222 : Item222) (hKW : KOfWellDefinedAll)
    (hThree : Item233ZRootGenThree) : Item233ZRootGen := by
  intro G _ _ A E U c L hpair hconc φ hφ Z hZ hKZ h4 h3 hR
  have hA : Nat.card A = 3 ^ 4 ∨ Nat.card A = 3 ^ 3 := by
    rcases hconc with ⟨-, -, hA⟩ | ⟨-, -, hA⟩ | ⟨-, -, hA⟩
    · exact Or.inl hA
    · exact Or.inr hA
    · exact Or.inr hA
  rcases hA with hA | hA
  · exact (Item221ResProof.rootGen_four h222 hKW hpair hA hφ hKZ (h4 hA)).trans le_sup_right
  · exact hThree G A E U c L hpair hconc hA φ hφ Z hZ hKZ (h3 hA) hR

end CFSG.RankThree.PartTwo.Sec21

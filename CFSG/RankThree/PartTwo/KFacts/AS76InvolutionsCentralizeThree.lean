module

public import CFSG.RankThree.PartTwo.Sec21.Item234
public import CFSG.RankThree.PartTwo.KFacts.AS76L44
public import CFSG.RankThree.PartTwo.KFacts.AS76Sp64
public import CFSG.RankThree.PartTwo.KFacts.AS76U58

public section

namespace CFSG.RankThree.PartTwo.Sec21

theorem as76InvolutionsCentralizeThree : AS76InvolutionsCentralizeThree := by
  intro X _ hX
  rcases hX with hX | hX | hX
  · obtain ⟨e⟩ := hX
    exact AS76.U58.invFixThree_projSU.of_mulEquiv e
  · obtain ⟨e⟩ := hX
    exact AS76.L44.invFixThree_projSL.of_mulEquiv e
  · obtain ⟨e⟩ := hX
    exact AS76.Sp64.invFixThree_projSp.of_mulEquiv e

end CFSG.RankThree.PartTwo.Sec21

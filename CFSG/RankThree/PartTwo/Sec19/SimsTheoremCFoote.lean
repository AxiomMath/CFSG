module

public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.AGLEmbedding

@[expose] def spOrder (n q : ℕ) : ℕ := q ^ (n ^ 2) * ∏ i ∈ Finset.Icc 1 n, (q ^ (2 * i) - 1)

end CFSG.RankThree.PartTwo.Sec19.SimsTheoremC

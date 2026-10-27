module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bFalse
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bA7
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM22
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bJ2
public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bL3

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem pieceA7M22_holds :
    PieceA7M22 := by
  unfold PieceA7M22
  intro G _ _ A c L E F a b R Y hY h
  rcases h with h | h
  · exact false_of_norm2e hY norm2_alt7.toNorm2e h
  · exact false_of_norm2e hY norm2_M22.toNorm2e h

theorem pieceHJ_holds :
    PieceHJ := by
  unfold PieceHJ
  intro G _ _ A c L E F a b R Y hY h
  exact false_of_norm2e hY norm2_J2.toNorm2e h

theorem pieceL3_holds : PieceL3 := by
  unfold PieceL3
  intro G _ _ A c L E F a b R Y hY h
  obtain ⟨p, e, hp, hp3, he1, he2, hiso⟩ := h
  haveI := hp
  rcases hiso with ⟨hq, ⟨eq⟩⟩ | ⟨hq, ⟨eq⟩⟩
  · exact false_of_norm2e hY (X := projSL 3 (GaloisField p e)) (norm2e_projSL p e hp3 he1 he2 hq)
      ⟨eq⟩
  · exact false_of_norm2e hY (X := projSU 3 p e) (norm2e_projSU p e hp3 he1 he2 hq) ⟨eq⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b

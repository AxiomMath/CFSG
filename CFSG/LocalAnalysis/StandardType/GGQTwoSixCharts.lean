module

public import CFSG.LocalAnalysis.StandardType.GGQTwoSixWin
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmChart
import CFSG.ClassicalInvolution.Phan.Center

public section

namespace CFSG.StandardType.QTwo.SixPoint

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]
  {H : Subgroup G}

theorem qTwoSix_fourChart_exists (hK : Nat.card K = 4) (B : QTwoCanonBlocks K 5 6 H) (s : ℕ)
    (hs : s + 4 ≤ 6) : ∃ φ : Su K 2 1 4 →* G, QTwoFourChart B s hs φ := by
  obtain ⟨φ, hker, hφ⟩ := B.exists_chart_of_embedding (by decide : 4 ≤ 5)
    (by decide : 5 ≤ 6) (qTwoSixWinEmb hs)
  let ι : Su K 2 1 4 →* Su K 2 1 5 := blockEmb K 2 1 5 4 0 (by decide)
  have he : qTwoSixWinEmb (m := 5) (k := 4) (i := 0) (by decide) =
      Fin.castLEEmb (by decide : 4 ≤ 5) := by
    ext a
    simp [qTwoSixWinEmb]
  refine ⟨φ.comp ι, ?_, ?_⟩
  · exact comp_blockEmb_injective (by simpa using hK) hker (by decide)
      (by decide : 4 < 5) (by decide : 3 ≤ 5)
  · intro J hJ
    have hJ4 : J.card ≤ 4 := by simpa using Finset.card_le_univ J
    calc
      B.blk (J.map (qTwoSixWinEmb hs)) =
          (coordBlockSU K 2 1 (J.map (Fin.castLEEmb (by decide : 4 ≤ 5)))).map φ :=
        hφ J hJ hJ4
      _ = ((coordBlockSU K 2 1 J).map ι).map φ := by
        rw [qTwoSix_map_win_coordBlock, he]
      _ = (coordBlockSU K 2 1 J).map (φ.comp ι) := by rw [Subgroup.map_map]

end CFSG.StandardType.QTwo.SixPoint

end

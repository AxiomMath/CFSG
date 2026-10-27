module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTriHat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTriNorm
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTriRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_tripleA6 (h : S16gRowCtx D V₀ V L hV)
    (hN : TripleA6Six (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L))) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨Q, _, _, L', N, hQ2, -, -, -, hnorm, hrk, htr⟩ := s16k_exists_quot_data h
  obtain ⟨K, i1, i2, Γ₀, hK, hdet, hHat, hsc, hR⟩ := hN
  obtain ⟨hL, hQ⟩ := s16k_hat_of_tripleA6 (L' := L') ⟨K, i1, i2, Γ₀, hK, hdet, hHat, hsc, htr _ hR⟩
  have h1 := s16k_pRank_normalizer_hat_a6 hQ2 hQ hL hnorm hp hp2
  have h2 := s16k_pRank_hat_a6_le_two hL hp hp2
  have h3 := h.three_le_pRank hpσ
  have h4 := hrk p hp
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

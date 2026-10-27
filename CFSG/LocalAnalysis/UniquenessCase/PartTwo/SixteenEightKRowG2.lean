module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKG2CentA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcAut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKG2Cent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_g2 (hU : S16kG2IsU33) (h : S16gRowCtx D V₀ V L hV)
    (hN : G2NaturalDerived (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 1) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨Q, _, _, L', N, -, -, -, -, hnorm, hrk, htr⟩ := s16k_exists_quot_data h
  obtain ⟨K, i1, i2, hK, hR⟩ := hN
  have hN' : G2NaturalDerived L' ⊤ ⊥ 1 := ⟨K, i1, i2, hK, htr _ hR⟩
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup (MulAut Q)) ≤ 0 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => by rw [le_bot_iff.1 hE]; simp
  have h1 := s16k_pRank_le_of_normalizer hnorm hp
  rw [s16k_centralizer_g2_trivial hN', inf_bot_eq] at h1
  have h2 := s16k_pRank_aut_u33 (s16k_b42TypeU33_of_g2 hU hN') hp hp2
  have h3 := h.three_le_pRank hpσ
  have h4 := hrk p hp
  split_ifs at h2 <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

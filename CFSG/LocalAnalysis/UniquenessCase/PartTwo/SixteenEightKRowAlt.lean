module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSmallShapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKAltEnd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKAltAut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKAltClose

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_altNatural (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement) {n : ℕ} (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n)
    (hN : AlternatingNatural (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) n) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hn5 := s16k_five_le_of_isAlt h.quasi hA
  obtain ⟨Q, _, _, L', N, -, -, ⟨eL⟩, -, hnorm, hrk, htr⟩ := s16k_exists_quot_data h
  have hC := s16k_centralizer_alt_trivial hn5 (htr _ hN)
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup (MulAut Q)) ≤ 0 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => by rw [le_bot_iff.1 hE]; simp
  have h1 := s16k_pRank_le_of_normalizer hnorm hp
  rw [hC, inf_bot_eq] at h1
  obtain ⟨eA⟩ := hA
  have h2 := s16k_pRank_aut_alt hn5 ⟨eL.symm.trans eA⟩ hp hp2
  have h3 : 3 ≤ n / p := (h.three_le_pRank hpσ).trans ((hrk p hp).trans (by omega))
  exact s16k_false_of_alt_fix h hn5 hN hp hp2 hpσ ((Nat.le_div_iff_mul_le hp.pos).1 h3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

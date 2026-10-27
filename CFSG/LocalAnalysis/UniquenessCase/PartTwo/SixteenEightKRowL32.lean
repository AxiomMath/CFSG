module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcAut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcSchur

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_l32 (h : S16gRowCtx D V₀ V L hV)
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L))
    (hS : IsL3 ↥(lBar V₀ V hV L) 1)
    (hm : E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) = 8) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨Q, hQc, hQf, L', N, h2, hcard, ⟨e⟩, hirrImp, hnorm, hrk, -⟩ :=
    s16k_exists_quot_data h
  letI := hQc
  letI := hQf
  have hQ8 : Nat.card Q = 2 ^ 8 := by rw [hcard, hm]
  have hirrQ := hirrImp hirr
  have hshape : IsL3 ↥L' 1 := CFSG.Blueprint.LieModel.of_mulEquiv e hS
  have h1 := s16k_pRank_le_of_normalizer hnorm hp
  have hcent : CFSG.Open.pRank p (Subgroup.centralizer (L' : Set (MulAut Q))) ≤ 1 := by
    refine (s16k_pRank_centralizer_le h2 hirrQ hQ8 hp hp2).trans ?_
    by_cases hord : orderOf (2 : ZMod p) ∣ 8 <;> simp [hord]
  have hmono : CFSG.Open.pRank p (N ⊓ Subgroup.centralizer (L' : Set (MulAut Q))) ≤
      CFSG.Open.pRank p (Subgroup.centralizer (L' : Set (MulAut Q))) :=
    CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right
  have haut := s16k_pRank_aut_l32 hshape hp hp2
  have h3 := h.three_le_pRank hpσ
  have h4 := hrk p hp
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

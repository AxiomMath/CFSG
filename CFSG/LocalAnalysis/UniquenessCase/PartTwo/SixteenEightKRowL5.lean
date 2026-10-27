module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKInputs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcAut
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcEmb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKExcRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem s16k_false_of_l5 (h : S16gRowCtx D V₀ V L hV) (hI2 : S16kEndF2Rank10)
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L))
    (hS : IsLn ↥(lBar V₀ V hV L) 5 1)
    (hm : E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) = 10) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  obtain ⟨Q, hQc, hQf, L', N, h2, hQ, ⟨e⟩, hirrImp, hnorm, hrk, -⟩ :=
    s16k_exists_quot_data h
  have hQ10 : Nat.card Q = 2 ^ 10 := by rw [hQ, hm]
  have hirrQ := hirrImp hirr
  have hshape : IsLn ↥L' 5 1 := CFSG.Blueprint.LieModel.of_mulEquiv e hS
  have hcent : Subgroup.centralizer (L' : Set (MulAut Q)) = ⊥ :=
    hI2 Q h2 hQ10 L' hirrQ (Or.inl hshape)
  have h1 := s16k_pRank_le_of_normalizer hnorm hp
  rw [hcent, inf_bot_eq] at h1
  have h0 : CFSG.Open.pRank p (⊥ : Subgroup (MulAut Q)) ≤ 0 :=
    CFSG.SectionRank.pRank_le hp.one_lt fun E hE _ => by rw [le_bot_iff.1 hE]; simp
  have h2' := s16k_pRank_aut_l5 hshape hp hp2
  have h3 := h.three_le_pRank hpσ
  have h4 := hrk p hp
  split_ifs at h2' <;> omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

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

theorem s16k_false_of_l34 (h : S16gRowCtx D V₀ V L hV)
    (hirr : commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L))
    (hS : IsLn ↥(lBar V₀ V hV L) 3 2)
    (hm : E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) = 9) : False := by
  obtain ⟨p, hpσ⟩ := h.std.hx.sig_nonempty
  have hp : p.Prime := (D.sig_prime p hpσ).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpσ).2
  have hrk3 : 3 ≤ CFSG.Open.pRank p (Mbar D.M V₀ V hV) := h.three_le_pRank hpσ
  obtain ⟨Q, hQc, hQf, L', N, hsq, hcardQ, hiso, hirrImp, hNL, hrank, -⟩ :=
    s16k_exists_quot_data h
  letI := hQc
  letI := hQf
  rw [hm] at hcardQ
  obtain ⟨e⟩ := hiso
  have hirrQ : ∀ B : Subgroup Q, (∀ l ∈ L', ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤ :=
    hirrImp hirr
  have hL34 : IsLn ↥L' 3 2 := CFSG.Blueprint.LieModel.of_mulEquiv e hS
  have hrkN : 3 ≤ CFSG.Open.pRank p N := hrk3.trans (hrank p hp)
  have hkey : CFSG.Open.pRank p N ≤ 2 := by
    have h1 := s16k_pRank_le_of_normalizer (Q := Q) (L' := L') (N := N) hNL hp
    have h2' := s16k_pRank_centralizer_le (Q := Q) (L := L') hsq hirrQ (d := 9) hcardQ hp hp2
    have h3 := s16k_pRank_aut_l34 (X := ↥L') hL34 hp hp2
    have hmono : CFSG.Open.pRank p (N ⊓ Subgroup.centralizer (L' : Set (MulAut Q)))
        ≤ CFSG.Open.pRank p (Subgroup.centralizer (L' : Set (MulAut Q))) :=
      CFSG.SectionRank.pRank_mono hp.one_lt inf_le_right
    refine h1.trans ?_
    by_cases hp3 : p = 3
    · have hnot : ¬ orderOf (2 : ZMod p) ∣ 9 := by
        rw [hp3]
        have hord : orderOf (2 : ZMod 3) = 2 :=
          orderOf_eq_prime (by decide) (by decide)
        rw [hord]
        norm_num
      rw [if_neg hnot] at h2'
      rw [if_pos hp3] at h3
      omega
    · have hbound : (if orderOf (2 : ZMod p) ∣ 9 then 1 else 0) ≤ 1 := by
        split <;> omega
      rw [if_neg hp3] at h3
      omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

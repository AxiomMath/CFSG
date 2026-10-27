module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps107Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FourDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Ctx
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Iso

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS (InChev2)
open scoped commutatorElement Pointwise

theorem w135_inGq_of_oddLieType {S : Type} [Group S] (h : CFSG.Blueprint.OddLieType S) :
    ∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 0 < e ∧ InGq S (p ^ e) := by
  obtain ⟨t, n, p, f, hp, hp2, hadm, hmod⟩ := h
  have hf : 1 ≤ f := hadm.2.1
  exact ⟨p, f, hp, hp2, by omega,
    Or.inl ⟨t, n, p, f, hp, hp2, by omega, rfl, hmod⟩⟩

theorem w135_odd_case
    (hAt : W4Lem13_5AtChev2) (h105 : W4Lem10_5Four) (h107 : W4Lem10_7Irr)
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3)
    (hodd : CFSG.Blueprint.OddLieType (↥L ⧸ Subgroup.center ↥L)) :
    W4Lem13_5Concl W Y L t := by
  obtain ⟨p, e, hp, hp2, he, hI⟩ := w135_inGq_of_oddLieType hodd
  have hctx' := hctx
  have hnorm : (L.subgroupOf Y).Normal := w135_normal_of_ctx hctx
  have hO2 : O2Trivial L := w135_o2Trivial_of_ctx hctx
  obtain ⟨-, -, hLY, hF, hq, -⟩ := hctx
  have hm3 : E3.mParam Y ≤ 3 := w135_mParam_le_three htY ht2 hm
  rcases h105 W hW Y L p e (p ^ e) hLY hnorm hF hq hO2 hp hp2 he rfl hI with
    h4 | h4g | h6g
  · exfalso; omega
  · rcases h4g with hU3 | hP4 | hL28 | ⟨hU43, hZ43⟩
    · exact hAt W hW Y L t hctx' htY ht2 hm
        (w135_inChev2_quotient_of_psu_three_three hq hU3)
    · exact hAt W hW Y L t hctx' htY ht2 hm
        (w135_inChev2_quotient_of_psp_two_three hq hP4)
    · exact hAt W hW Y L t hctx' htY ht2 hm
        (w135_inChev2_quotient_of_psl_two_eight hq hL28)
    · obtain ⟨⟨S, hGS, hSU, hhat⟩, hrk⟩ := h107 W hW Y L t hctx' hU43 hZ43 htY ht2 hm
      exact W4Lem13_5Concl.of_hatU43
        ⟨S, hGS, hSU, hhat, by rw [w135_card_eq_two_pow_rk hW, hrk]⟩
  · rcases h6g with h5 | h7 | h9
    · exact hAt W hW Y L t hctx' htY ht2 hm (w135_inChev2_of_psl_two_five h5)
    · exact hAt W hW Y L t hctx' htY ht2 hm (w135_inChev2_of_psl_two_seven h7)
    · exact hAt W hW Y L t hctx' htY ht2 hm (w135_inChev2_of_psl_two_nine h9)

end CFSG.LocalAnalysis.WeakClosure81

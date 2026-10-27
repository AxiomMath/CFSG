module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumDet
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem ggQ2_posInL_lineE6 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) : GGQ2GammaNbrPosInLOn GGQ2SelE6 := by
  intro G _ _ p B Bs x L D J hS hp hI hxL _ y K hnb hnr hM hE u hu
  subst hp
  obtain ⟨N, hE6, hpos⟩ := hE
  have hdet0 : ((N.cartan.det : ℤ) : ZMod 3) = 0 := by
    obtain ⟨e, he⟩ := hE6
    have hC : GGIntCartan (CoxeterMatrix.E₆.reindex e) N.cartan := by
      rw [← he]
      exact N.isCartan
    have hC0 : GGIntCartan (CoxeterMatrix.E₆.reindex e)
        (Matrix.reindex e e (CartanMatrix.E 6)) := ggIntCartan_E₆.reindex e
    have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.E₆.reindex e) :=
      ggAtMostOneMultipleEdge_E₆.reindex e
    have hdet : N.cartan.det = (CartanMatrix.E 6).det := by
      rcases hC.eq_or_eq_transpose hC0 hone with h | h
      · rw [h, Matrix.det_reindex_self e (CartanMatrix.E 6)]
      · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e (CartanMatrix.E 6)]
    rw [hdet, CartanMatrix.E₆_det, ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num
  exact ggQ2_gammaNbr_of_detDatum hLB hP h5 hS rfl hI hnb N hdet0 hpos hu

end CFSG.StandardType

end

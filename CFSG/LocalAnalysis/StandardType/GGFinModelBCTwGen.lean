module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelBCIso

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.StandardType CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.HardMathSupport.Timmesfeld.LangTorus

section TwGen

private theorem ggRatEmb_frobQ_aux
    (f : ℕ) (c : GaloisField 2 (2 * f)) :
    ggRatEmb (2 * f) (frobQ 2 f c) = (ggRatEmb (2 * f) c) ^ 2 ^ f := by
  rw [frobQ_apply, map_pow]

@[expose] noncomputable def ggTwPsi
    (f : ℕ) :
    ↥(e6Data_valid.minGroup (GaloisField 2 (2 * f))) →* ModGL (langTag .twistedE6) GGL :=
  (baseChangeGL (ggRatEmb (2 * f))).comp
    ((adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))).subtype.comp
      (e6IsogenyT (GaloisField 2 (2 * f))))

theorem ggTwPsi_xm
    (f : ℕ) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (c : GaloisField 2 (2 * f)) :
    ggTwPsi f (e6Data_valid.xm (GaloisField 2 (2 * f)) a c) =
      pinnedX (langTag .twistedE6) GGL a (ggRatEmb (2 * f) c) := by
  change baseChangeGL (ggRatEmb (2 * f))
      (((e6Isogeny (GaloisField 2 (2 * f))
        (e6Data_valid.xm (GaloisField 2 (2 * f)) a c) :
        ↥(adjointGroup .E6 (GaloisField 2 (2 * f)))) :
        ModGL .E6 (GaloisField 2 (2 * f)))) =
    pinnedX .E6 GGL a (ggRatEmb (2 * f) c)
  rw [ggE6_isogeny_xm_pinned (GaloisField 2 (2 * f)) ha c]
  exact baseChangeGL_pinnedX (ggRatEmb (2 * f)) a c

theorem ggTwSigma_xm
    (f : ℕ) {a : Fin (Tag.rank .E6) → ℤ} (ha : IsRoot .E6 a)
    (c : GaloisField 2 (2 * f)) :
    sigma (GaloisField 2 (2 * f)) (frobQ 2 f) (e6Data_valid.xm (GaloisField 2 (2 * f)) a c) =
      e6Data_valid.xm (GaloisField 2 (2 * f)) (rho a) (frobQ 2 f c) := by
  rw [sigma_xm (frobQ 2 f) ha c]
  have h : (twistSign a : GaloisField 2 (2 * f)) = 1 := by
    rcases twistSign_eq_one_or a with h | h
    · rw [h, Int.cast_one]
    · rw [h, Int.cast_neg, Int.cast_one]
      exact CharTwo.neg_eq 1
  rw [h, one_mul]

theorem ggTwPsi_sigma
    (f : ℕ) (g : ↥(e6Data_valid.minGroup (GaloisField 2 (2 * f)))) :
    ggPhi .twistedE6 f (ggTwPsi f g) =
      ggTwPsi f (sigma (GaloisField 2 (2 * f)) (frobQ 2 f) g) := by
  have h : (ggPhi .twistedE6 f).comp (ggTwPsi f) =
      (ggTwPsi f).comp (sigma (GaloisField 2 (2 * f)) (frobQ 2 f)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (closure_xm_simple_eq_top e6Data_valid (GaloisField 2 (2 * f))) ?_
    rintro _ ⟨i, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply]
      rw [ggTwPsi_xm f (isRoot_single .E6 i) c]
      rw [ggPhi_pinnedX_twistedE6 f (isRoot_single .E6 i) (ggRatEmb (2 * f) c)]
      rw [ggTwSigma_xm f (isRoot_single .E6 i) c]
      rw [ggTwPsi_xm f (isRoot_rho (isRoot_single .E6 i)) (frobQ 2 f c)]
      rw [ggRatEmb_frobQ_aux f c]
      rfl
    · simp only [MonoidHom.comp_apply]
      rw [ggTwPsi_xm f (isRoot_neg_single .E6 i) c]
      rw [ggPhi_pinnedX_twistedE6 f (isRoot_neg_single .E6 i) (ggRatEmb (2 * f) c)]
      rw [ggTwSigma_xm f (isRoot_neg_single .E6 i) c]
      rw [ggTwPsi_xm f (isRoot_rho (isRoot_neg_single .E6 i)) (frobQ 2 f c)]
      rw [ggRatEmb_frobQ_aux f c]
      rfl
  simpa only [MonoidHom.comp_apply] using DFunLike.congr_fun h g

theorem ggIotaK_twistedE6_apply
    (n f : ℕ) (hf : 1 ≤ f) (g : (ggU .twistedE6 n f).K) :
    ggIotaK .twistedE6 n f hf g =
      ggTwPsi f ((fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype g) := by
  let g' : twistedE6Group 2 f := g
  change ggIotaK .twistedE6 n f hf g' =
    ggTwPsi f ((fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype g')
  rw [ggIotaK, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [ggIota_twistedE6_mk]
  change baseChangeGL (ggRatEmb (2 * f))
      (((twistedE6Isogeny 2 f hf g' : ↥⁅twistedFixedGroup TwistTag.E6
        (GaloisField 2 (2 * f)) (frobQ 2 f),
        twistedFixedGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)⁆) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) =
    baseChangeGL (ggRatEmb (2 * f))
      ((adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))).subtype
        ((e6IsogenyT (GaloisField 2 (2 * f)))
          ((fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f)).subtype g')))
  rw [coe_twistedE6Isogeny]
  rfl

end TwGen

end CFSG.StandardType.GGFinModel

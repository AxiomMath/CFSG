module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeOuterInn

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SeitzReduction.TwistedE6Pilot


theorem le_inner_of_commute_outer_involution {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    {t : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))}
    (ht2 : t ^ 2 = 1) (htI : t ∉ LayerSixE.twInndiagAut f)
    {X : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
      (frobQ 2 f)))}
    (hXel : IsElemAbelian 3 X) (hXI : X ≤ LayerSixE.twInndiagAut f)
    (hXt : ∀ x ∈ X, t * x = x * t) :
    X ≤ (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
        (frobQ 2 f)) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f))
          (frobQ 2 f))).range :=
  fun x hx =>
    mem_range_conj_of_mem_twInndiag_of_commute_outer_involution hf ht2 htI
      (hXI hx) (hXt x hx)

end CFSG.StandardType.NoOffTwE6Three

module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructTwE6
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructTwE6Levi
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructTwE6Pieces

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.LieType.Steinberg.Exceptional

theorem KGTwE6.kgPiecesD_stdRepC_twE6 {f : ℕ} (hf : 1 ≤ f) :
    KGND.KGPiecesD (LayerSixE.twInndiagAut f) (stdRepC (frobQ_frobQ 2 f hf) 0) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  have hσ : ∀ c, frobQ 2 f c = c ^ 2 ^ f := frobQ_apply 2 f
  exact KGTwE6.kgPiecesD_stdRepC_twE6_of hf (KGTwE6.su6LeviHom hK hσ)
    (KGTwE6.su6LeviHom_surjective hK hσ) (KGTwE6.largeEvenMarking_su6Levi hf hK hσ)
    (KGTwE6.exists_suConjSet_compatParamAut hK hσ)

theorem ggRootCentKGStructTag_twistedE6 : GGRootCentKGStructTag .twistedE6 :=
  ggRootCentKGStructTag_twistedE6_of fun _ hf => KGTwE6.kgPiecesD_stdRepC_twE6 hf

end CFSG.StandardType

end

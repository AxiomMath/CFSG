module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomyBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2x_model_nsmul {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

end CFSG.StandardType

end

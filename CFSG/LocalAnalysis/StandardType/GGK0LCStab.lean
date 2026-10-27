module

public import CFSG.LocalAnalysis.StandardType.GGK0LCDefs
public import CFSG.LocalAnalysis.StandardType.GGK0LCDescent
public import CFSG.LocalAnalysis.StandardType.GGK0LCCentred

public section

namespace CFSG.StandardType.GGK0LC

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace KacPt


theorem stab_le_refl
    {τ : Tag} (hT : KacBox τ) {d : ℕ} (hc : KacCentred τ d)
    (K : KacPt τ) (hp : K.p.Prime) (hd : ¬ K.p ∣ d) : K.stab ≤ K.refl :=
  stab_le_refl_of_free hT K fun _ hz h => inv_eq_empty_imp_one hT hc K hp hd hz h

end KacPt

end CFSG.StandardType.GGK0LC

end

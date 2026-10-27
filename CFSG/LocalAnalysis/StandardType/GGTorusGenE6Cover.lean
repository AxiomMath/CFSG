module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6Defs
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer

public section

namespace CFSG.StandardType.E6ThreeModel

open CFSG CFSG.Assembly TableB

theorem isComponentOf_map_ggFix_of_central {L' R : Type} [Group L'] [Group R] [Finite L']
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {a : MulAut L'} {b : MulAut R} (hab : ∀ l, b (ψ l) = ψ (a l))
    {J : Subgroup L'} (hJ : IsComponentOf J (ggFix a)) : IsComponentOf (J.map ψ) (ggFix b) := by
  exact LayerCC.isComponentOf_map_ggFix hψ hker (fun l => (hab l).symm) hJ

end CFSG.StandardType.E6ThreeModel

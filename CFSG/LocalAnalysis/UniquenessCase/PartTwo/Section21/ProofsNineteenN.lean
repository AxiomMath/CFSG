module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
import CFSG.GroupTheory.ComponentFStarProd
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Quasithin.Background.F1Models
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightLayer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_nonempty_mulEquiv_fstar_of_ne (D : Data G) {L K : Subgroup G}
    (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hLK : L ≠ K) {A B : Type} [Group A]
    [IsSimpleGroup A] [Group B] (hB : ∀ a b : B, a * b = b * a) :
    ¬ Nonempty (↥(CFSG.Open.genFittingFStar (Bar2 D.M)) ≃* A × B) := by
  rintro ⟨φ⟩
  have hcomp : barImage D.M L = barImage D.M K :=
    CFSG.GroupTheory.eq_of_isComponent_of_mulEquiv_prod hB φ
      (PartTwo.s13_barImage_isComponent hL) (PartTwo.s13_barImage_isComponent hK)
  exact hLK (barImage_injOn_calC hL hK hcomp)

end CFSG.LocalAnalysis.UniquenessCase.UC22

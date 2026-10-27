module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.A4Defs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Gap6R2

variable {G : Type} [Group G] [Finite G]

theorem inf_le_of_isSylowTwoOf_sup {S T X : Subgroup G} (hST : S ≤ T) (hT : IsPGroup 2 T)
    (hS : IsSylowTwoOf S (X ⊔ S)) : T ⊓ X ≤ S := by
  have hP : IsPGroup 2 ↥(S ⊔ (T ⊓ X)) :=
    hT.to_le (sup_le hST inf_le_left)
  have hle : S ⊔ (T ⊓ X) ≤ X ⊔ S := sup_le le_sup_right (inf_le_right.trans le_sup_left)
  exact le_sup_right.trans (((A4.isSylowTwoOf_iff_maximal).mp hS).2.2 _ hle hP le_sup_left)

end Gap6R2

end CFSG.Quasithin

module

public import CFSG.RankThree.PartOne.FOC.AltFamily
public import CFSG.RankThree.PartOne.FOC.PSUFive
public import CFSG.RankThree.PartOne.FOC.CenterSU5
public import CFSG.RankThree.PartOne.FOC.SpFamily
public import CFSG.RankThree.PartOne.FOC.OrthFamily
public import CFSG.RankThree.PartOne.FOC.ListProvider
public import CFSG.RankThree.PartOne.FOCD.Final

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem FOC.fieldInnerLie_classical (hdefI : FOC.DefInnerComponent) (hdefO : FOC.DefOuterComponent)
    (t : StatedLieTag) (ℓ : ℕ) (ht : t ∈ classicalTags) : FOC.FieldInnerLie t ℓ := by
  have h6 : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus := by
    revert ht
    cases t <;> simp [classicalTags]
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact FOC.fieldInnerLie_PSL'' hdefI hdefO ℓ
  · exact FOC.fieldInnerLie_PSU_final hdefI hdefO ℓ
  · exact FOC.fieldInnerLie_PSp hdefI ℓ
  · exact FOC.fieldInnerLie_POmegaOdd hdefI hdefO ℓ
  · exact FOC.fieldInnerLie_POmegaPlus hdefI hdefO ℓ
  · exact FOC.fieldInnerLie_POmegaMinus hdefI hdefO ℓ

theorem fieldOnComponentOuter_of_residuals
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (h68 : SectionProvider Sec68Hyp) (hSLB : N143.SectionListBound)
    (hSpor : FOC.FieldInnerSpor) (hExc : FOC.FieldInnerExc) : FieldOnComponentOuter :=
  fieldOnComponentOuter_of_cases hbridge h68 (FOC.sectionProviderK_listNative hSLB)
    FOC.fieldInnerAlt hSpor
    (fun t ℓ ht => FOC.fieldInnerLie_classical FOCD.defInnerComponent FOCD.defOuterComponent t
      ℓ ht)
    hExc FOC.fieldInnerCenter

end CFSG.RankThree.PartOne

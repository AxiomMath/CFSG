module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialSelfCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SupDecomposition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

theorem not_isCyclic_centralizer_of_mem_sup
    {G : Type} [Group G] [Finite G] {Q C P : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hPC : P ≤ Q ⊔ C)
    (hCQ : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c)
    {y : G} (hy : y ∈ P) :
    ¬ IsCyclic (Subgroup.centralizer ({y} : Set G) ⊓ Q : Subgroup G) := by
  obtain ⟨q, hq, c, hc, rfl⟩ := exists_mul_mem_sup_of_commute hCQ (hPC hy)
  exact not_isCyclic_centralizer_extraspecial_mul_central hQ hq (fun x hx => hCQ c hc x hx)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

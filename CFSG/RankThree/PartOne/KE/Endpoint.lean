module

public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem component_odd_conclusion_of_native {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G))
    {T : Type*} [Group T] (e : T ≃* L ⧸ Subgroup.center L) (hodd : PlaneLocalCoreOdd p T) :
    ComponentLocalCoreOddConclusion p E t L ∧
      (E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨hset, hWN, hodd', -, hnonf⟩ := component_local_core_odd_action_of_plane hp hp2 hE
    hEcard ht ht1 hL hEL hSL (PlaneLocalCoreOdd.of_mulEquiv hp e.symm hodd)
  exact ⟨⟨hset, hWN, hodd'⟩, hnonf⟩

theorem actual_component_endpoint_of_native {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G))
    {T : Type*} [Group T] (e : T ≃* L ⧸ Subgroup.center L) (hodd : PlaneLocalCoreOdd p T)
    (hcore : LocalCoreTrivialOn p fun α : MulAut T => α ∉ (MulAut.conj : T →* MulAut T).range) :
    ComponentLocalCoreOddConclusion p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
          Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) := by
  obtain ⟨h1, h2⟩ := component_odd_conclusion_of_native hp hp2 hE hEcard ht ht1 hL hEL hSL e hodd
  refine ⟨h1, ?_⟩
  rintro (hC | hnon)
  · exact h2 hC
  · exact (noninner_component_local_core_product_centralizes hp hp2 hE hEcard ht ht1 hL hEL hSL e
      hcore hnon).2

end CFSG.RankThree.PartOne.KE

module

public import CFSG.RankThree.PartOne.KC.SymplecticOrthogonalEndpointStatements

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.RankThree.GroupTheory
open scoped Pointwise

theorem inner_actual_component_of_planeLocalCoreInner {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (htE : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({t} : Set G)) ≤
      Subgroup.normalizer (L : Set G))
    {T' : Type} [Group T'] (ξ : L ⧸ Subgroup.center L ≃* T')
    {P' : Subgroup (MulAut T') → Prop} (hint : PlaneLocalCoreInner p T' P')
    (hside : actualPlane L E ≤
        (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range →
      P' ((actualPlane L E).map (MulAut.congr ξ).toMonoidHom)) :
    ComponentLocalCoreNormalizes p E t L ∧
      ((E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
          actualPlane L E ≤
            (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) →
        localCoreProduct p E t ≤ Subgroup.centralizer (L : Set G)) := by
  have hp2 : p ≠ 2 := by omega
  have hplaneL := PlaneLocalCoreInner.of_mulEquiv hp ξ hint
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t htE ht1
  have hWN : localCoreProduct p E t ≤ Subgroup.normalizer (L : Set G) := by
    refine sup_le (commutator_le_normalizer_of_le hSL hEL) ?_
    exact (iInf_le_of_le t (iInf_le_of_le htE (iInf_le _ ht1))).trans hSL
  refine ⟨⟨hset, hWN⟩, fun hinn => ?_⟩
  have hP : E ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥ ∨
      (P' ((actualPlane L E).map (MulAut.congr ξ).toMonoidHom) ∧
        actualPlane L E ≤
          (MulAut.conj : (L ⧸ Subgroup.center L) →* MulAut (L ⧸ Subgroup.center L)).range) := by
    rcases hinn with h1 | h2
    · exact Or.inl h1
    · exact Or.inr ⟨hside h2, h2⟩
  exact (component_local_core_centralizes_of_inner_plane hp hp2 hE hEcard htE ht1 hL hEL hSL
    hplaneL hP).2.2

end CFSG.RankThree.PartOne

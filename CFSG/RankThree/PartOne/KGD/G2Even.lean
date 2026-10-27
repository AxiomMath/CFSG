module

public import CFSG.RankThree.PartOne.KGD.PlaneBridge
public import CFSG.RankThree.PartOne.KE.Endpoint
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenCrossPrimeLocalCore
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.LocalRank CFSG.RankThree.Chevalley
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

theorem planeLocalCoreOdd_G2_even {f : ℕ} (hf : 2 ≤ f) (K : Type)
    [Field K] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    PlaneLocalCoreOdd p (adjointGroup .G2 K) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos two_pos f).ne')
  have : Finite (adjointGroup .G2 K) := inferInstance
  refine planeLocalCoreOdd_of_subgroup_form hp fun B hB E hE hEcard t htE ht1 => ?_
  exact (even_G2_cross_prime_local_core_product_odd hf K hK hp hp3 B hB E hE hEcard t htE ht1).2.2.2.1

theorem g2_even_component {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) {f : ℕ} (hT : ChevalleyExceptionalModel (L ⧸ center L) .G2 2 f)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G)) :
    ComponentLocalCoreOddConclusion p E t L ∧
      (E ⊓ centralizer (L : Set G) ≠ ⊥ → localCoreProduct p E t ≤ centralizer (L : Set G)) := by
  obtain ⟨⟨-, hf1, -, h3⟩, hmod⟩ := hT
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    subst this
    omega
  exact KE.component_odd_conclusion_of_native hp (by omega) hE hEcard ht ht1 hL hEL hSL e
    (planeLocalCoreOdd_G2_even hf2 K hK hp hp3)

end CFSG.RankThree.PartOne.KGD

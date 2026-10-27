module

public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.RankThree.Chevalley.SteinbergCFOddE7NoninnerCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddE8InnerField

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open scoped Pointwise

theorem odd_E7_noninner_cross_prime_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hT : ChevalleyExceptionalModel (L ⧸ center L) .E7 ℓ f)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hnon : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
        Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hT.2
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup .E7 K) =>
      α ∉ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (odd_E7_noninner_odd_prime_field_descent_and_local_core_trivial hℓ hℓ2 hf K hK hp
        (by omega) B hB α hα hαp).2.2
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e hcore hnon

theorem odd_E8_noninner_cross_prime_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hT : ChevalleyExceptionalModel (L ⧸ center L) .E8 ℓ f)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hnon : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range) :
    ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E :
        Subgroup G) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G) ∧
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E ≤
        centralizer (L : Set G) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hT.2
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup .E8 K) =>
      α ∉ (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (odd_E8_inner_field_automorphisms_and_noninner_prime_core hℓ hℓ2 hf K
        hK).2.2.2.2.2.2 hp B hB α hα hαp
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e hcore hnon

end CFSG.RankThree.Chevalley

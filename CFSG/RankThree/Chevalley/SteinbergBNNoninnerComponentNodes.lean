module

public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.RankThree.Chevalley.SteinbergBTEvenF4Noninner
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE7E8Noninner
public import CFSG.RankThree.Chevalley.SteinbergCFOddF4NoninnerLocalCore

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open scoped Pointwise

theorem odd_G2_noninner_cross_prime_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f) (hT : ChevalleyExceptionalModel (L ⧸ center L) .G2 ℓ f)
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
  have hNF := conj_normalForm_of_pointwise
    (odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2
      (Or.inr ⟨rfl, hℓ3⟩)).1
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup .G2 K) =>
      α ∉ (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp => by
      obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
      exact (odd_Chevalley_inner_field_noninner_prime_local_core_trivial .G2 hℓ hℓ2 hf K hK hNF
        hp B hB α hα hαp x σ hxσ).2.2.2
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e hcore hnon

theorem odd_F4_noninner_actor_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hT : ChevalleyExceptionalModel (L ⧸ center L) .F4 ℓ f)
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
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup .F4 K) =>
      α ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (odd_F4_noninner_prime_local_core_trivial hℓ hℓ2 hf K hK hp B hB).1 α hα hαp
  exact noninner_component_local_core_product_centralizes hp hp2 hE hEcard ht ht1 hL hEL hSL
    e hcore hnon

theorem even_F4_noninner_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {f : ℕ} (hf : 1 ≤ f)
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .F4 2 f)
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
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime :=
    finite_field_prime_power_characteristic Nat.prime_two hf hK
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup .F4 K) =>
      α ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp => by
      obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α.1
      exact (even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hK hp (by omega)
        B hB α hα hαp x a a.2 hxa).2.2.2.2
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e hcore hnon

theorem even_E6_noninner_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {f : ℕ} (hf : 1 ≤ f)
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .E6 2 f)
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
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions .E6 (Or.inl rfl) K
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup .E6 K) =>
      α ∉ (MulAut.conj : adjointGroup .E6 K →* MulAut (adjointGroup .E6 K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hK Θ hΘ hp hp3 B
        hB α hα hαp).2.2
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e hcore hnon

theorem even_E7_E8_noninner_actual_component_local_core_product_centralizes {G : Type}
    [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    {τ : Assembly.LowTwoRank.StatedLieTag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f)
    (hT : ChevalleyExceptionalModel (L ⧸ center L) τ 2 f)
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
  obtain ⟨τ', hτ', hU⟩ : ∃ τ' : Tag, (τ' = .E7 ∨ τ' = .E8) ∧
      UntwistedChevalleyModel (L ⧸ center L) τ' (2 ^ f) := by
    rcases hτ with rfl | rfl
    · exact ⟨.E7, Or.inl rfl, hT.2⟩
    · exact ⟨.E8, Or.inr rfl, hT.2⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hU
  have hNF := conj_normalForm_of_pointwise
    (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ' hτ').1
  have hcore : LocalCoreTrivialOn p fun α : MulAut (adjointGroup τ' K) =>
      α ∉ (MulAut.conj : adjointGroup τ' K →* MulAut (adjointGroup τ' K)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp => by
      obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
      exact (even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ' hτ' hf K hK hp B
        hB α hα hαp x σ hxσ).2.2.2
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e hcore hnon

end CFSG.RankThree.Chevalley

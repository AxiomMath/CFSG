module

public import CFSG.RankThree.Chevalley.SteinbergBNComponentLocalCoreReduction
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.LieType.Chevalley.OddExceptionalOuterTwoRank

public section

namespace CFSG.RankThree.Chevalley

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open scoped Pointwise

theorem triality_noninner_actual_component_local_core_product_centralizes {G : Type} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {E : Subgroup G}
    (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E)
    (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L) {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hT : ChevalleyExceptionalModel (L ⧸ center L) .trialityD4 ℓ f)
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
  have hm : TwistedChevalleyModel (L ⧸ center L) .D4 (ℓ ^ f) := hT.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hℓ hf hm
  have hK3 : Nat.card K = (ℓ ^ f) ^ 3 := hK
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
      ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ := by
    rcases eq_or_ne ℓ 2 with rfl | hℓ2
    · obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hf K hK3 σ hσ
      exact ⟨Θ, hΘ⟩
    · obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ :=
        odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK3 σ hσ
      exact ⟨Θ, hΘ⟩
  have hcore : LocalCoreTrivialOn p
      fun α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =>
        α ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
          MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range :=
    localCoreTrivialOn_of_forall hp fun B hB α hα hαp =>
      (triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK3 σ hσ Θ hΘ
        hp hp3 B hB α hα hαp).2.2.2
  exact noninner_component_local_core_product_centralizes hp (by omega) hE hEcard ht ht1 hL hEL
    hSL e.symm hcore hnon

end CFSG.RankThree.Chevalley

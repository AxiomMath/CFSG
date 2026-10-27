module

public import CFSG.RankThree.PartOne.KC.LinearTwoPlaneBridge
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

@[expose] def LinearTwoPlaneCoreInput : Prop :=
  ∀ {ℓ f : ℕ}, ℓ.Prime → ∀ {K : Type} [Field K], Nat.card K = ℓ ^ f →
    ∀ {B : Subgroup (Equiv.Perm (Omega K))}, coordinateG K ≤ B → B ≤ coordinateE K →
    ∀ {p : ℕ}, p.Prime → 3 < p → ∀ {A : Subgroup B}, IsElemAbelian p A →
    Nat.card A = p ^ 2 → ∀ {a : B}, a ∈ A → a ≠ 1 →
      Odd (Nat.card (KCLinearTwo.abstractPlaneProduct p A a)) ∧
      (p = ℓ → ∀ x ∈ A, x ≠ 1 →
        inSubgroup (aschbacherSolvableCore p) (centralizer ({x} : Set B)) = ⊥) ∧
      (p ≠ ℓ → p ∣ f)

namespace KCLinearTwo

theorem planeLocalCore_coordinateG (hCE : LinearTwoPlaneCoreInput) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    {K : Type} [Field K] (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    PlaneLocalCoreOdd p (coordinateG K) ∧
      (p = ℓ → PlaneLocalCoreBot p (coordinateG K) (fun _ => True)) ∧
      (p ≠ ℓ → PlaneDivides p (coordinateG K) f) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨?_, fun hpℓ => ?_, fun hpℓ => ?_⟩
  · intro B hB A hAB hA hAcard t htA ht1
    obtain ⟨B', hGB, hBE, A', a, hA', hA'card, haA', ha1, hcard, -⟩ :=
      planeData_coordinateG hp B hB A hAB hA hAcard htA
    have hodd := (hCE hℓ hK hGB hBE hp hp3 hA' hA'card haA' (ha1 ht1)).1
    rw [hcard]
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  · intro B hB A hAB hA hAcard _ t htA ht1
    obtain ⟨B', hGB, hBE, A', a, hA', hA'card, haA', ha1, -, hbot⟩ :=
      planeData_coordinateG hp B hB A hAB hA hAcard htA
    have h3 := (hCE hℓ hK hGB hBE hp hp3 hA' hA'card haA' (ha1 ht1)).2.1 hpℓ
    have hθ := h3 a haA' (ha1 ht1)
    have hT : thetaT p A' = ⊥ := le_bot_iff.mp (by
      calc thetaT p A' ≤ inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set B')) :=
            (iInf_le _ a).trans ((iInf_le _ haA').trans (iInf_le _ (ha1 ht1)))
        _ = ⊥ := hθ)
    exact hbot (by rw [abstractPlaneProduct, hθ, hT, Subgroup.commutator_bot_left, bot_sup_eq])
  · intro B hB A hAB hA hAcard
    have hAne : A ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hAcard
      have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
      omega
    obtain ⟨t, ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    obtain ⟨B', hGB, hBE, A', a, hA', hA'card, haA', ha1, -⟩ :=
      planeData_coordinateG hp B hB A hAB hA hAcard t.2
    exact (hCE hℓ hK hGB hBE hp hp3 hA' hA'card haA' (ha1 (fun h => ht (Subtype.ext h)))).2.2
      hpℓ

end KCLinearTwo

theorem linear_two_normalized_component_local_core_product_odd_image_of
    (hCE : LinearTwoPlaneCoreInput) : LinearTwoNormalizedComponentLocalCoreProductOddImage := by
  intro G _ _ p hp hp3 E hE hEcard t htE ht1 L hL ℓ f k _ _ hℓ hf hk h4 ⟨φ⟩ hEL hSL
  have hp2 : p ≠ 2 := by omega
  have ψ : (L ⧸ center L) ≃* coordinateG k :=
    φ.trans ((LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 k).symm.trans
      (pslEquivCoordinateG k))
  obtain ⟨hodd, hbot, hdiv⟩ := KCLinearTwo.planeLocalCore_coordinateG hCE hℓ hk hp hp3
  have hoddT : PlaneLocalCoreOdd p (L ⧸ center L) := PlaneLocalCoreOdd.of_mulEquiv hp ψ hodd
  obtain ⟨hset, hWN, hrel, hres, hnonfaith⟩ := component_local_core_odd_action_of_plane hp hp2 hE
    hEcard htE ht1 hL hEL hSL hoddT
  refine ⟨⟨⟨hset, hWN, hrel⟩, hres⟩, fun hpℓ => ?_, fun hC hpℓ => ?_⟩
  · by_cases hC : E ⊓ Subgroup.centralizer (L : Set G) = ⊥
    · subst hpℓ
      have hbotT := PlaneLocalCoreBot.of_mulEquiv hp ψ (hbot rfl)
      exact plane_reduction_bot hp hp2 hE hEcard htE ht1 hL hEL hSL hC hbotT trivial
    · exact hnonfaith hC
  · exact plane_reduction_division hp hp2 hE hEcard htE ht1 hL hEL hSL hC
      (PlaneDivides.of_mulEquiv hp ψ (hdiv hpℓ))

end CFSG.RankThree.PartOne

module

public import CFSG.Timmesfeld.Orders.ExceptionalTwistedBruhat
public import CFSG.Timmesfeld.Orders.ExceptionalTwistedUnipotent

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {t : TwistTag} {K : Type} [Field K] [Finite K] {σ : K →+* K} {q : ℕ}

omit [Finite K] in
theorem card_graphFixedRootBorel (hσ : Function.Surjective σ) :
    Nat.card (graphFixedRootBorel t K σ) =
      Nat.card (graphFixedRootTorus t K σ) * Nat.card (graphFixedPosUnipotent t K σ) := by
  have hbij : Set.BijOn (fun p : ModGL t.tag K × ModGL t.tag K => p.1 * p.2)
      ((graphFixedRootTorus t K σ : Set (ModGL t.tag K)) ×ˢ
        (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)))
      (graphFixedRootBorel t K σ : Set (ModGL t.tag K)) := by
    refine ⟨fun p hp => ?_, fun p hp p' hp' h => ?_, fun x hx => ?_⟩
    · rw [graphFixedRootBorel_eq_mul hσ]
      exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    · obtain ⟨h1, h2⟩ := graphFixedRoot_mul_unique hp.1 hp'.1 hp.2 hp'.2 h
      exact Prod.ext h1 h2
    · rw [graphFixedRootBorel_eq_mul hσ] at hx
      obtain ⟨h, hh, u, hu, rfl⟩ := hx
      exact ⟨(h, u), ⟨hh, hu⟩, rfl⟩
  calc Nat.card (graphFixedRootBorel t K σ) = Nat.card ((graphFixedRootTorus t K σ :
        Set (ModGL t.tag K)) ×ˢ (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K))) :=
        Nat.card_congr hbij.equiv.symm
    _ = _ := by
      rw [Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
      rfl

theorem card_graphFixedRootGroup_eq (hσ : Function.Surjective σ) :
    Nat.card (graphFixedRootGroup t K σ) = Nat.card (graphFixedRootBorel t K σ) *
      ∑ᶠ w : relWeylTwist t, Nat.card (graphFixedInversionUnipotent t K σ w) := by
  classical
  have : Fintype (relWeylTwist t) := Fintype.ofFinite _
  have : Finite (Module.End K (RootModule t.tag K)) := Module.finite_of_finite K
  have e : (graphFixedRootGroup t K σ : Set (ModGL t.tag K)) ≃
      Σ w : relWeylTwist t, graphFixedRootBruhatCell t K σ w := by
    rw [graphFixedRootGroup_eq_iUnion hσ]
    exact Set.unionEqSigmaOfDisjoint fun w w' h =>
      disjoint_graphFixedRootBruhatCell fun h' => h (Subtype.ext h')
  have hcell : ∀ w : relWeylTwist t, Nat.card (graphFixedRootBruhatCell t K σ w) =
      Nat.card (graphFixedRootBorel t K σ) * Nat.card (graphFixedInversionUnipotent t K σ w) := by
    intro w
    rw [← Nat.card_congr (bijOn_graphFixedRootBruhatCell hσ w.2).equiv,
      Nat.card_congr (Equiv.Set.prod _ _), Nat.card_prod]
    rfl
  calc Nat.card (graphFixedRootGroup t K σ) =
        Nat.card (Σ w : relWeylTwist t, graphFixedRootBruhatCell t K σ w) := Nat.card_congr e
    _ = ∑ w : relWeylTwist t, Nat.card (graphFixedRootBruhatCell t K σ w) := Nat.card_sigma
    _ = _ := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => hcell w

open Classical in
theorem card_graphFixedRootGroup [Fintype (WeylGroup t.tag)] (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card) :
    Nat.card (graphFixedRootGroup t K σ) = Nat.card (compatTorus (t := t) σ) *
      q ^ {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α}.ncard *
        ∑ w ∈ Finset.univ.filter (· ∈ relWeylTwist t), q ^ (coxeterSystem t.tag).length w := by
  rw [card_graphFixedRootGroup_eq hσ, card_graphFixedRootBorel hσ,
    graphFixedRootTorus_eq_compatTorus hσ, card_graphFixedPosUnipotent hσ hq,
    finsum_eq_sum_of_fintype]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter (· ∈ relWeylTwist t)) (fun w => by simp)
    (fun w => Nat.card (graphFixedInversionUnipotent t K σ w))]
  refine Finset.sum_congr rfl fun w hw => ?_
  exact card_graphFixedInversionUnipotent hσ hq (Finset.mem_filter.1 hw).2

omit [Finite K] in
theorem compatDiag_injective :
    Function.Injective (compatDiag t σ) := by
  intro u v h
  funext a
  have h1 := congrFun h (t.orbitMin a)
  rw [compatDiag_orbitMin, compatDiag_orbitMin] at h1
  exact Units.ext (Subtype.ext (congrArg Units.val h1))

omit [Finite K] in
theorem card_compatSubgroup :
    Nat.card (compatSubgroup (t := t) σ) = ∏ a, (Nat.card (orbitField t K σ a) - 1) := by
  classical
  have hrange : Set.range (compatDiag t σ) = (compatSubgroup (t := t) σ : Set _) := by
    ext c
    refine ⟨?_, fun hc => exists_compatDiag_eq (σ := σ) hc⟩
    rintro ⟨u, rfl⟩
    exact fun i => compatDiag_perm u i
  rw [← SetLike.coe_sort_coe, ← hrange, Nat.card_range_of_injective compatDiag_injective,
    Nat.card_pi]
  exact Finset.prod_congr rfl fun a _ => Nat.card_units _

end CFSG.Timmesfeld.ExceptionalOrders

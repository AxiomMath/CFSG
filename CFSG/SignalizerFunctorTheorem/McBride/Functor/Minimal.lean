module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Lift
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSubgroupIndices
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {Cl : SigClass.{u}} {G : Type u} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
  {θ : G → Subgroup G}

private theorem card_lt_of_ne_top {K : Subgroup G} (h : K ≠ ⊤) : Nat.card K < Nat.card G := by
  have proper : K < ⊤ := lt_top_iff_ne_top.mpr h
  simpa only [Subgroup.card_top] using
    CFSG.SignalizerFunctor.Helpers.subgroup_card_strict_mono proper

private theorem exists_greatest_le_of_subgroup (hCl : IsSigClass p Cl)
    (hA : IsElemAbelian p A) (hθ : IsFunctor p A θ) (hC : ∀ a ∈ A, a ≠ 1 → Cl G A (θ a))
    (IH : CompleteBelow p Cl (Nat.card G) (Nat.card A)) {K : Subgroup G} (hAK : A ≤ K)
    (hKlt : Nat.card K < Nat.card G) :
    ∃ W ∈ signalizers p A θ (Cl G A), W ≤ K ∧
      ∀ Y ∈ signalizers p A θ (Cl G A), Y ≤ K → Y ≤ W := by
  have hmapA : (A.subgroupOf K).map K.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAK]
  have hAe : IsElemAbelian p (A.subgroupOf K) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_subgroupOf p A K hA
  have hcard : Nat.card (A.subgroupOf K) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hfun : IsFunctor p (A.subgroupOf K) (pullFunctor K.subtype θ) := by
    refine IsFunctor.pullFunctor K.subtype K.subtype_injective ?_
    rw [hmapA]
    exact hθ
  have hAKn : A ≤ Subgroup.normalizer (K : Set G) := hAK.trans Subgroup.le_normalizer
  have hPP : ∀ Y : Subgroup K, Cl K (A.subgroupOf K) Y ↔ Cl G A (Y.map K.subtype) := by
    intro Y
    rw [hCl.map_iff K G K.subtype K.subtype_injective (A.subgroupOf K) Y, hmapA]
  have hcl : ∀ a ∈ A.subgroupOf K, a ≠ 1 →
      Cl K (A.subgroupOf K) (pullFunctor K.subtype θ a) := by
    intro a ha ha1
    rw [hPP]
    have ha' : (a : G) ∈ A := ha
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hmap : (pullFunctor K.subtype θ a).map K.subtype = θ a ⊓ K := by
      change ((θ (K.subtype a)).comap K.subtype).map K.subtype = θ (K.subtype a) ⊓ K
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
    rw [hmap]
    exact hCl.mono G inf_le_left (CFSG.SignalizerFunctor.Helpers.normalizer_inf_of_le A _ _
      (hθ.normalized _ ha' ha1') hAKn) (hC _ ha' ha1')
  have hcomplete := IH K hKlt (A.subgroupOf K) (pullFunctor K.subtype θ) hAe hcard hfun hcl
  rw [isCompleteIn_signalizers_pullFunctor_iff K.subtype K.subtype_injective hPP, hmapA,
    Subgroup.range_subtype] at hcomplete
  exact hcomplete

theorem eq_bot_of_normal_of_incomplete (hp : p.Prime) (hCl : IsSigClass p Cl)
    (hA : IsElemAbelian p A) (hθ : IsFunctor p A θ) (hC : ∀ a ∈ A, a ≠ 1 → Cl G A (θ a))
    (IH : CompleteBelow p Cl (Nat.card G) (Nat.card A))
    (hinc : ¬ IsCompleteIn (signalizers p A θ (Cl G A))) {N : Subgroup G} [N.Normal]
    (hN : N ∈ signalizers p A θ (Cl G A)) : N = ⊥ := by
  by_contra hne
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hkerc : Nat.Coprime p (Nat.card π.ker) := by
    rw [hker]
    exact hN.2.1
  have hf : Set.InjOn π A := injOn_of_coprime_ker hp hA hkerc
  have hinj : Function.Injective (π.domRestrict A) :=
    CFSG.SignalizerFunctor.Helpers.actor_image_injective_of_coprime_kernel p hp π A
      (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A hA) hkerc
  have hlt : Nat.card (G ⧸ N) < Nat.card G := by
    have h1 : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hne
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have h3 : 0 < Nat.card (G ⧸ N) := Nat.card_pos
    nlinarith
  have hAe : IsElemAbelian p (A.map π) :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_image p π A hA
  have hcard : Nat.card (A.map π) = Nat.card A :=
    CFSG.SignalizerFunctor.Helpers.subgroup_image_card_of_injective π A hinj
  have hfun := hθ.imageFunctor hp hA hf
  have hcl : ∀ x ∈ A.map π, x ≠ 1 → Cl (G ⧸ N) (A.map π) (imageFunctor π A θ x) :=
    fun x hx hx1 => cl_imageFunctor_apply hCl hp hA hθ hN.2.1 hC hx hx1
  exact hinc (isCompleteIn_of_quotient hCl hp hA hθ hN
    (IH (G ⧸ N) hlt (A.map π) (imageFunctor π A θ) hAe hcard hfun hcl))

theorem isLocallyCompleteIn_of_incomplete (hp : p.Prime) (hCl : IsSigClass p Cl)
    (hA : IsElemAbelian p A) (hθ : IsFunctor p A θ) (hC : ∀ a ∈ A, a ≠ 1 → Cl G A (θ a))
    (IH : CompleteBelow p Cl (Nat.card G) (Nat.card A))
    (hinc : ¬ IsCompleteIn (signalizers p A θ (Cl G A))) :
    IsLocallyCompleteIn (signalizers p A θ (Cl G A)) := by
  intro X hX hX1
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := hX.1
  have hne : Subgroup.normalizer (X : Set G) ≠ ⊤ := by
    intro h
    have : X.Normal := Subgroup.normalizer_eq_top_iff.mp h
    exact hX1 (eq_bot_of_normal_of_incomplete hp hCl hA hθ hC IH hinc hX)
  obtain ⟨W, hW, hWK, hmax⟩ :=
    exists_greatest_le_of_subgroup hCl hA hθ hC IH hAX (card_lt_of_ne_top hne)
  exact ⟨W, hW, hWK, fun Z hZ hZK => hmax Z hZ hZK⟩

theorem sSup_signalizers_sup_eq_top (_hp : p.Prime) (hCl : IsSigClass p Cl)
    (hA : IsElemAbelian p A) (hθ : IsFunctor p A θ) (hC : ∀ a ∈ A, a ≠ 1 → Cl G A (θ a))
    (IH : CompleteBelow p Cl (Nat.card G) (Nat.card A))
    (hinc : ¬ IsCompleteIn (signalizers p A θ (Cl G A))) :
    sSup (signalizers p A θ (Cl G A)) ⊔ A = ⊤ := by
  by_contra hne
  obtain ⟨W, hW, hWK, hmax⟩ := exists_greatest_le_of_subgroup hCl hA hθ hC IH
    (le_sup_right : A ≤ sSup (signalizers p A θ (Cl G A)) ⊔ A) (card_lt_of_ne_top hne)
  exact hinc ⟨W, hW, fun Y hY => hmax Y hY ((le_sSup hY).trans le_sup_left)⟩

theorem minimal_counterexample_structure (hp : p.Prime) (hCl : IsSigClass p Cl)
    (hA : IsElemAbelian p A) (hθ : IsFunctor p A θ) (hC : ∀ a ∈ A, a ≠ 1 → Cl G A (θ a))
    (IH : CompleteBelow p Cl (Nat.card G) (Nat.card A))
    (hinc : ¬ IsCompleteIn (signalizers p A θ (Cl G A))) :
    sSup (signalizers p A θ (Cl G A)) ⊔ A = ⊤ ∧
      (∀ N : Subgroup G, N.Normal → N ∈ signalizers p A θ (Cl G A) → N = ⊥) ∧
      IsLocallyCompleteIn (signalizers p A θ (Cl G A)) :=
  ⟨sSup_signalizers_sup_eq_top hp hCl hA hθ hC IH hinc,
    fun _ _ hNm => eq_bot_of_normal_of_incomplete hp hCl hA hθ hC IH hinc hNm,
    isLocallyCompleteIn_of_incomplete hp hCl hA hθ hC IH hinc⟩

end CFSG.SignalizerFunctorTheorem.McBride

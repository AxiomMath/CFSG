module

public import CFSG.Quasithin.Background.F918Z8Sz7Ga
public import CFSG.Quasithin.Background.F918H3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

section ChiefMin

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem chief_exists_irr {X A : Subgroup (MulAut Y)} {M : Subgroup Y} {t : MulAut Y}
    (hX : commutator ↥X = ⊤) (hXM : ∀ x ∈ X, ∀ w ∈ M, x w ∈ M)
    (hAM : ∀ a ∈ A, ∀ w ∈ M, a w ∈ M) (htM : ∀ w ∈ M, t w ∈ M)
    (hAX : A ≤ Subgroup.normalizer (X : Set (MulAut Y))) (htX : ∀ x ∈ X, t * x = x * t)
    (hnt : ∃ x ∈ X, ∃ w ∈ M, x w ≠ w) :
    ∃ I J : Subgroup Y, J < I ∧ I ≤ M ∧ X ≤ stabSub I ∧ X ≤ stabSub J ∧
      A ≤ stabSub I ∧ A ≤ stabSub J ∧ (∀ w ∈ I, t w ∈ I) ∧ (∀ w ∈ J, t w ∈ J) ∧
      (∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) →
        (∀ a ∈ A, ∀ s ∈ T, a s ∈ T) → (∀ s ∈ T, t s ∈ T) → T = J ∨ T = I) ∧
      (∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ J) := by
  classical
  let 𝓢 : Set (Subgroup Y) := {I | I ≤ M ∧ (∀ x ∈ X, ∀ w ∈ I, x w ∈ I) ∧
    (∀ a ∈ A, ∀ w ∈ I, a w ∈ I) ∧ (∀ w ∈ I, t w ∈ I) ∧ ∃ x ∈ X, ∃ w ∈ I, x w * w⁻¹ ∉ fixV X}
  have hM : M ∈ 𝓢 := by
    refine ⟨le_rfl, hXM, hAM, htM, ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, w, hw, hne⟩ := hnt
    exact hne (chief_perfect_fixes hX (fun x' hx' => hcon x' hx' w hw) x hx)
  have : Finite (Subgroup Y) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨I, hI, hmin⟩ := Set.exists_min_image 𝓢 (fun I => Nat.card ↥I) (Set.toFinite 𝓢) ⟨M, hM⟩
  obtain ⟨hIM, hXI, hAI, htI, x₀, hx₀, w₀, hw₀, hnt₀⟩ := hI
  set J : Subgroup Y := I ⊓ fixV X with hJ
  have hXJ' : ∀ x ∈ X, ∀ j ∈ J, x j ∈ J := fun x hx j hj => by
    rw [hj.2 x hx]
    exact hj
  have hAJ' : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := by
    intro a ha j hj
    refine ⟨hAI a ha j hj.1, fun x hx => ?_⟩
    have hx' : a⁻¹ * x * a ∈ X := by
      have := (Subgroup.mem_normalizer_iff.1 (hAX (A.inv_mem ha)) x).1 hx
      simpa using this
    have e : x * a = a * (a⁻¹ * x * a) := by group
    calc x (a j) = (x * a) j := rfl
      _ = (a * (a⁻¹ * x * a)) j := by rw [e]
      _ = a ((a⁻¹ * x * a) j) := rfl
      _ = a j := by rw [hj.2 _ hx']
  have htJ' : ∀ j ∈ J, t j ∈ J := by
    intro j hj
    refine ⟨htI j hj.1, fun x hx => ?_⟩
    calc x (t j) = (x * t) j := rfl
      _ = (t * x) j := by rw [← htX x hx]
      _ = t (x j) := rfl
      _ = t j := by rw [hj.2 x hx]
  have hJI : J < I := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h' : I ⊓ fixV X = I := h
    have hIX : I ≤ fixV X := inf_eq_left.1 h'
    apply hnt₀
    rw [hIX hw₀ x₀ hx₀, mul_inv_cancel]
    exact (fixV X).one_mem
  have hirr : ∀ T : Subgroup Y, J ≤ T → T ≤ I → (∀ x ∈ X, ∀ s ∈ T, x s ∈ T) →
      (∀ a ∈ A, ∀ s ∈ T, a s ∈ T) → (∀ s ∈ T, t s ∈ T) → T = J ∨ T = I := by
    intro T hJT hTI hXT hAT htT
    by_cases hTI' : T = I
    · exact Or.inr hTI'
    · left
      have hTS : T ∉ 𝓢 := fun hT => hTI' (Subgroup.eq_of_le_of_card_ge hTI (hmin T hT))
      have hTX : ∀ x ∈ X, ∀ s ∈ T, x s * s⁻¹ ∈ fixV X := by
        by_contra hcon
        push Not at hcon
        obtain ⟨x, hx, s, hs, hns⟩ := hcon
        exact hTS ⟨hTI.trans hIM, hXT, hAT, htT, x, hx, s, hs, hns⟩
      have hTfix : ∀ s ∈ T, s ∈ fixV X := fun s hs x hx =>
        chief_perfect_fixes hX (fun x' hx' => hTX x' hx' s hs) x hx
      exact le_antisymm (fun s hs => ⟨hTI hs, hTfix s hs⟩) hJT
  exact ⟨I, J, hJI, hIM, le_stabSub_of_forall_mem hXI, le_stabSub_of_forall_mem hXJ',
    le_stabSub_of_forall_mem hAI, le_stabSub_of_forall_mem hAJ', htI, htJ', hirr,
    x₀, hx₀, w₀, hw₀, fun h => hnt₀ h.2⟩

end ChiefMin

end CFSG.Quasithin

module

public import CFSG.Timmesfeld.ARS.Sec5Root
public import CFSG.Timmesfeld.ARS.Sec5Eight
public import CFSG.Timmesfeld.ARS.Sec5Count

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec5

theorem closure_rootElts_eq_top (hR : IsRootClass R) : Subgroup.closure (rootElts R) = ⊤ := by
  refine eq_top_iff.2 (hR.gen ▸ iSup₂_le fun A hA a ha => ?_)
  by_cases ha1 : a = 1
  · rw [ha1]
    exact Subgroup.one_mem _
  · exact Subgroup.subset_closure ⟨A, hA, ha, ha1⟩

theorem conjSet_conjSet (Δ : Set (Subgroup G)) (e g : G) :
    conjSet (conjSet Δ e) g = conjSet Δ (g * e) :=
  (conjSet_mul Δ g e).symm

theorem atMostTwo_conjSet {Δ : Set (Subgroup G)}
    (h2 : ∀ (X : Subgroup G) (g₁ g₂ g₃ : G), X ∈ conjSet Δ g₁ → X ∈ conjSet Δ g₂ →
      X ∈ conjSet Δ g₃ → conjSet Δ g₁ = conjSet Δ g₂ ∨ conjSet Δ g₁ = conjSet Δ g₃ ∨
        conjSet Δ g₂ = conjSet Δ g₃) (e : G) :
    ∀ (X : Subgroup G) (g₁ g₂ g₃ : G), X ∈ conjSet (conjSet Δ e) g₁ →
      X ∈ conjSet (conjSet Δ e) g₂ → X ∈ conjSet (conjSet Δ e) g₃ →
      conjSet (conjSet Δ e) g₁ = conjSet (conjSet Δ e) g₂ ∨
        conjSet (conjSet Δ e) g₁ = conjSet (conjSet Δ e) g₃ ∨
          conjSet (conjSet Δ e) g₂ = conjSet (conjSet Δ e) g₃ := by
  intro X g₁ g₂ g₃
  simp only [conjSet_conjSet]
  exact h2 X _ _ _

theorem second_conjSet {Δ : Set (Subgroup G)}
    (hsec : ∀ P ∈ Δ, ∃ g : G, P ∈ conjSet Δ g ∧ conjSet Δ g ≠ Δ) (e : G) :
    ∀ P ∈ conjSet Δ e, ∃ g : G, P ∈ conjSet (conjSet Δ e) g ∧
      conjSet (conjSet Δ e) g ≠ conjSet Δ e := by
  intro P hP
  have hP' : conjSub P e⁻¹ ∈ Δ := (mem_conjSet).1 hP
  obtain ⟨g, hPg, hg⟩ := hsec _ hP'
  refine ⟨e * g * e⁻¹, ?_, ?_⟩
  · rw [conjSet_conjSet, show e * g * e⁻¹ * e = e * g by group, conjSet_mul]
    have := conjSub_mem_conjSet hPg e
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
  · rw [conjSet_conjSet, show e * g * e⁻¹ * e = e * g by group, conjSet_mul]
    exact fun h => hg (conjSet_injective e h)

section Ten

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A) {Δ : Set (Subgroup G)}
include hR hiso hnd hΩ

theorem conjSet_mem_rootConj (hΔ : IsWeakTI R Δ)
    (hsec : ∀ P ∈ Δ, ∃ g : G, P ∈ conjSet Δ g ∧ conjSet Δ g ≠ Δ)
    (h2 : ∀ (X : Subgroup G) (g₁ g₂ g₃ : G), X ∈ conjSet Δ g₁ → X ∈ conjSet Δ g₂ →
      X ∈ conjSet Δ g₃ → conjSet Δ g₁ = conjSet Δ g₂ ∨ conjSet Δ g₁ = conjSet Δ g₃ ∨
        conjSet Δ g₂ = conjSet Δ g₃)
    {Θ : Set (Subgroup G)} (hΘ : Θ ∈ rootConj R Δ) {f : G} (hf : f ∈ rootElts R) :
    conjSet Θ f ∈ rootConj R Δ := by
  by_contra hnot
  obtain ⟨e, he, rfl⟩ := hΘ
  set Θ := conjSet Δ e with hΘdef
  have hΘw : IsWeakTI R Θ := isWeakTI_conjSet hR hΔ e
  have hΘW : Θ ∈ rootConj R Δ := ⟨e, he, rfl⟩
  have hne : conjSet Θ f ≠ Θ := fun h => hnot (by rw [h]; exact hΘW)
  have hdisj : Θ ∩ conjSet Θ f = ∅ := by
    rcases ((isWeakTI_iff hR).1 hΘw).2.2.2 f hf with h | h
    · exact h
    · exact absurd h hne
  obtain ⟨F, hFR, hfF, hf1⟩ := hf
  have hFc : ∀ D ∈ Θ, ¬ Commuting F D := by
    intro D hD hFD
    have hDf : conjSub D f = D := conjSub_of_forall_commute fun x hx => hFD f hfF x hx
    have : D ∈ Θ ∩ conjSet Θ f := ⟨hD, hDf ▸ conjSub_mem_conjSet hD f⟩
    rw [hdisj] at this
    exact this
  obtain ⟨A₁, hA₁, hA₁F⟩ := exists_opposite_of_forall_not_commuting hR hiso hnd hΩ hΘw hFR hFc
  obtain ⟨X, hX, hXA⟩ : ∃ X ∈ Θ, X ≠ A₁ := by
    obtain ⟨Y, hY, Y', hY', hYY'⟩ := hΘw.2.1
    by_cases h : Y = A₁
    · exact ⟨Y', hY', fun e => hYY' (h.trans e.symm)⟩
    · exact ⟨Y, hY, h⟩
  have hXl := mem_lambdaSet hR hiso hnd hΩ hΘw hA₁ hX (Ne.symm hXA)
  obtain ⟨B, ⟨hBR, hBle, hBψ⟩, -⟩ :=
    existsUnique_mem_psiSet_of_le hR hiso (hΘw.1 hA₁) hFR hA₁F hXl
  have hBΘ : B ∈ Θ := mem_of_le_sup hR hiso hΘw hA₁ hX hXl hBR hBle
  have hBfl : conjSub B f ∈ lambdaSet R B :=
    QD.conjSub_mem_lambdaSet_of_special hR hiso hFR hBR hBψ.2 hfF hf1
  have hBfΘf : conjSub B f ∈ conjSet Θ f := conjSub_mem_conjSet hBΘ f
  have hBfΘ : conjSub B f ∉ Θ := fun h => by
    have : conjSub B f ∈ Θ ∩ conjSet Θ f := ⟨h, hBfΘf⟩
    rw [hdisj] at this
    exact this
  obtain ⟨g, hBg, hg⟩ := second_conjSet hsec e B hBΘ
  have hBfg := mem_conjSet_of_mem_lambdaSet hR hiso hnd hΩ hΘw (second_conjSet hsec e)
    (atMostTwo_conjSet h2 e) hBΘ hBfl hBfΘ hBg hg
  obtain ⟨Θ', hΘ'W, hBfΘ'⟩ := exists_mem_rootConj hR hiso hnd hΩ hΔ (hR.conjSub_mem hBR f)
  obtain ⟨d', hd', rfl⟩ := hΘ'W
  rw [hΘdef, conjSet_conjSet] at hBfΘf hBfg
  rcases h2 _ (f * e) (g * e) d' hBfΘf hBfg hBfΘ' with h | h | h
  ·
    rw [← conjSet_conjSet, ← conjSet_conjSet, ← hΘdef] at h
    have : B ∈ Θ ∩ conjSet Θ f := ⟨hBΘ, h ▸ hBg⟩
    rw [hdisj] at this
    exact this
  · rw [← conjSet_conjSet, ← hΘdef] at h
    exact hnot (h ▸ ⟨d', hd', rfl⟩)
  ·
    rw [← conjSet_conjSet, ← hΘdef] at h
    exact hg (eq_of_mem_rootConj hR hiso hnd hΩ hΔ hsec h2 (h ▸ ⟨d', hd', rfl⟩) hΘW hBg hBΘ)

theorem isTI_of_atMostTwo (hΔ : IsWeakTI R Δ)
    (h2 : ∀ (X : Subgroup G) (g₁ g₂ g₃ : G), X ∈ conjSet Δ g₁ → X ∈ conjSet Δ g₂ →
      X ∈ conjSet Δ g₃ → conjSet Δ g₁ = conjSet Δ g₂ ∨ conjSet Δ g₁ = conjSet Δ g₃ ∨
        conjSet Δ g₂ = conjSet Δ g₃) : IsTI R Δ := by
  refine ⟨hΔ.1, hΔ.2.1, hΔ.2.2.1, fun g => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne, hneq⟩ := hcon
  obtain ⟨A, hA, hAg⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hgΔ : conjSet Δ g ≠ Δ := fun h => hneq (by rw [h, Set.inter_self])
  have hsec : ∀ P ∈ Δ, ∃ x : G, P ∈ conjSet Δ x ∧ conjSet Δ x ≠ Δ := by
    intro P hP
    obtain ⟨h, hh, hAh⟩ := exists_mem_stabSet_conjSub_eq hR hiso hnd hΩ hΔ hA hP
    refine ⟨h * g, ?_, ?_⟩
    · rw [conjSet_mul, ← hAh]
      exact conjSub_mem_conjSet hAg h
    · rw [conjSet_mul]
      intro e
      apply hgΔ
      have h1 := congrArg (fun Θ => conjSet Θ h⁻¹) e
      simp only [conjSet_conjSet_inv] at h1
      rw [h1]
      exact mem_stabSet.1 (Subgroup.inv_mem _ hh)
  have hall : ∀ x : G, conjSet Δ x ∈ rootConj R Δ := by
    intro x
    have hx : x ∈ Subgroup.closure (rootElts R) := by
      rw [closure_rootElts_eq_top hR]
      exact Subgroup.mem_top x
    induction hx using Subgroup.closure_induction_left with
    | one => exact ⟨1, Or.inl rfl, rfl⟩
    | mul_left y hy z _ ih =>
      rw [conjSet_mul]
      exact conjSet_mem_rootConj hR hiso hnd hΩ hΔ hsec h2 ih hy
    | inv_mul_cancel y hy z _ ih =>
      obtain ⟨Y, hY, hyY, hy1⟩ := hy
      rw [hR.inv_eq hY hyY, conjSet_mul]
      exact conjSet_mem_rootConj hR hiso hnd hΩ hΔ hsec h2 ih ⟨Y, hY, hyY, hy1⟩
  exact hgΔ (eq_of_mem_rootConj hR hiso hnd hΩ hΔ hsec h2 (hall g) ⟨1, Or.inl rfl,
    (conjSet_one Δ).symm⟩ hAg hA)

theorem isTI_of_four_le (hΔ : IsWeakTI R Δ) {A : Subgroup G} (hA : A ∈ Δ) {m : ℕ}
    (hm : Nat.card ↥(gen Δ) = Nat.card A ^ m) (h4 : 4 ≤ m) : IsTI R Δ := by
  refine isTI_of_atMostTwo hR hiso hnd hΩ hΔ fun X g₁ g₂ g₃ h₁ h₂ h₃ => ?_
  by_contra! hcon
  obtain ⟨h12, h13, h23⟩ := hcon
  have hΔ₁ := isWeakTI_conjSet hR hΔ g₁
  have hm₁ : Nat.card ↥(gen (conjSet Δ g₁)) = Nat.card X ^ m := by
    rw [card_gen_conjSet, hm, hR.card_eq (hΔ.1 hA) (hΔ₁.1 h₁)]
  have e₂ : conjSet (conjSet Δ g₁) (g₂ * g₁⁻¹) = conjSet Δ g₂ := by
    rw [conjSet_conjSet, inv_mul_cancel_right]
  have e₃ : conjSet (conjSet Δ g₁) (g₃ * g₁⁻¹) = conjSet Δ g₃ := by
    rw [conjSet_conjSet, inv_mul_cancel_right]
  exact false_of_three hR hiso hnd hΩ hΔ₁ h₁ hm₁ h4 (by rw [e₂]; exact h₂) (by rw [e₃]; exact h₃)
    (by rw [e₂]; exact Ne.symm h12) (by rw [e₃]; exact Ne.symm h13) (by rw [e₂, e₃]; exact h23)

end Ten

end Sec5

theorem isWeakTI_structure (h : Hyp G R) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ)
    {A : Subgroup G} (hA : A ∈ Δ) :
    CoveredBy R (gen Δ) ∧ (∀ B ∈ R, B ≤ gen Δ → B ∈ Δ) ∧
      ∃ m : ℕ, Nat.card ↥(gen Δ) = Nat.card A ^ m ∧
        Nat.card Δ * (Nat.card A - 1) = Nat.card A ^ m - 1 ∧ (m ≤ 3 ∨ IsTI R Δ) := by
  have := h.finite
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
    fun A hA B hB hBA => eq_of_omegaSet_eq h hA hB hBA
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow hR hiso hnd hΩ hΔ hA
  refine ⟨Sec5.coveredBy_gen hR hiso hnd hΩ hΔ,
    fun B hB hle => Sec5.mem_of_le_gen hR hiso hnd hΩ hΔ subset_rfl hB hle, m, hm, ?_, ?_⟩
  · rw [← hm]
    exact Sec5.card_mul_card_sub_one hR hiso hnd hΩ hΔ hA
  · by_cases hm3 : m ≤ 3
    · exact Or.inl hm3
    · exact Or.inr (Sec5.isTI_of_four_le hR hiso hnd hΩ hΔ hA hm (by omega))

end CFSG.Timmesfeld.ARS

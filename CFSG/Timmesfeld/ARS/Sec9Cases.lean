module

public import CFSG.Timmesfeld.ARS.Sec9SL2

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

@[expose] def IsBlock (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Blk : Set (Subgroup G)) :
    Prop :=
  Blk ⊆ leviSet R A A₀ ∧ ∀ Y ∈ Blk, comp R A A₀ Y ⊆ Blk

@[expose] def OrbitCollinear (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Blk : Set (Subgroup G)) :
    Prop :=
  ∀ B ∈ lambdaStar R A A₀, ∀ X ∈ lambdaStar R A A₀, ∃ Y ∈ orbit Blk X, Y ∈ lambdaSet R B

@[expose] def CollinearComp (R : Set (Subgroup G)) (A A₀ : Subgroup G) (Δ : Set (Subgroup G)) :
    Prop :=
  ∀ Y ∈ Δ, ∀ X ∈ lambdaStar R A A₀, Commuting Y X → X ∈ lambdaSet R Y

section Cases

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hmax hA₀

omit hmax in
theorem isBlock_of_mem {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) : IsBlock R A A₀ Δ := by
  refine ⟨fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hY, fun Y hY => ?_⟩
  obtain ⟨E, -, rfl⟩ := hΔ
  rw [comp_eq_of_mem hY]

omit h hA hAne hmax hA₀ in
theorem nonempty_of_mem {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) : Δ.Nonempty := by
  obtain ⟨E, -, rfl⟩ := hΔ
  exact ⟨E, self_mem_comp A A₀ E⟩

theorem levi_cases_of
    (hH3 : ∀ Δ₁ ∈ leviComps R A A₀, ¬ IsSL2Comp Δ₁ → OrbitCollinear R A A₀ Δ₁)
    (hH6 : ∀ Blk, IsBlock R A A₀ Blk → OrbitCollinear R A A₀ Blk → ∀ Δ ∈ leviComps R A A₀,
      (∀ Y ∈ Δ, Y ∉ Blk) → CollinearComp R A A₀ Δ)
    (hH8 : ∀ Blk, IsBlock R A A₀ Blk → OrbitCollinear R A A₀ Blk → ∀ Δ₂ ∈ leviComps R A A₀,
      (∀ Y ∈ Δ₂, Y ∉ Blk) → (∀ Δ ∈ leviComps R A A₀, (∀ Y ∈ Δ, Y ∉ Blk) → Δ = Δ₂) →
        IsSL2Comp Δ₂)
    (hr : 1 < Nat.card (leviComps R A A₀)) :
    (Nat.card (leviComps R A A₀) = 2 ∧ ∃ Δ₁ ∈ leviComps R A A₀, ∃ Δ₂ ∈ leviComps R A A₀,
      Δ₁ ≠ Δ₂ ∧ ¬ IsSL2Comp Δ₁ ∧ IsSL2Comp Δ₂) ∨
    (Nat.card (leviComps R A A₀) = 3 ∧ ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ) := by
  by_cases hall : ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ
  · exact Or.inr ⟨card_leviComps_eq_three h hA hAne hmax hA₀ hr hall, hall⟩
  push Not at hall
  obtain ⟨Δ₁, hΔ₁, hS₁⟩ := hall
  have hcard : Nat.card (leviComps R A A₀) = (leviComps R A A₀).ncard :=
    Nat.card_coe_set_eq _
  have hdisj : ∀ {Δ Δ' : Set (Subgroup G)}, Δ ∈ leviComps R A A₀ → Δ' ∈ leviComps R A A₀ →
      Δ ≠ Δ' → ∀ Y ∈ Δ, Y ∉ Δ' := by
    rintro Δ Δ' ⟨E, -, rfl⟩ ⟨F, -, rfl⟩ hne Y hY hY'
    exact hne (comp_eq_comp hY hY')
  rcases Nat.lt_or_ge (Nat.card (leviComps R A A₀)) 4 with h4 | h4
  · rcases (by omega : Nat.card (leviComps R A A₀) = 2 ∨ Nat.card (leviComps R A A₀) = 3)
      with h2 | h3
    ·
      left
      rw [hcard, Set.ncard_eq_two] at h2
      obtain ⟨X, Y, hXY, hXYs⟩ := h2
      obtain ⟨Δ₂, hΔ₂, h12, hother⟩ : ∃ Δ₂ ∈ leviComps R A A₀, Δ₁ ≠ Δ₂ ∧
          ∀ Δ ∈ leviComps R A A₀, Δ = Δ₁ ∨ Δ = Δ₂ := by
        have hmem : ∀ Δ ∈ leviComps R A A₀, Δ = X ∨ Δ = Y := fun Δ hΔ => by
          rw [hXYs] at hΔ
          simpa using hΔ
        rcases hmem Δ₁ hΔ₁ with rfl | rfl
        · exact ⟨Y, hXYs ▸ (by simp), hXY, fun Δ hΔ => hmem Δ hΔ⟩
        · exact ⟨X, hXYs ▸ (by simp), Ne.symm hXY,
            fun Δ hΔ => (hmem Δ hΔ).elim Or.inr Or.inl⟩
      refine ⟨by rw [hcard, Set.ncard_eq_two]; exact ⟨X, Y, hXY, hXYs⟩, Δ₁, hΔ₁, Δ₂, hΔ₂, h12,
        hS₁, hH8 Δ₁ (isBlock_of_mem h hA hAne hA₀ hΔ₁) (hH3 Δ₁ hΔ₁ hS₁) Δ₂ hΔ₂
        (hdisj hΔ₂ hΔ₁ (Ne.symm h12)) fun Δ hΔ hout => ?_⟩
      rcases hother Δ hΔ with rfl | rfl
      · obtain ⟨Y, hY⟩ := nonempty_of_mem hΔ
        exact absurd hY (hout Y hY)
      · rfl
    ·
      exfalso
      rw [hcard, Set.ncard_eq_three] at h3
      obtain ⟨X, Y, Z, hXY, hXZ, hYZ, hXYZ⟩ := h3
      have hmem : ∀ Δ ∈ leviComps R A A₀, Δ = X ∨ Δ = Y ∨ Δ = Z := fun Δ hΔ => by
        rw [hXYZ] at hΔ
        simpa using hΔ
      have hXm : X ∈ leviComps R A A₀ := hXYZ ▸ (by simp)
      have hYm : Y ∈ leviComps R A A₀ := hXYZ ▸ (by simp)
      have hZm : Z ∈ leviComps R A A₀ := hXYZ ▸ (by simp)
      obtain ⟨Δa, hΔa, Δb, hΔb, hab, h1a, h1b, hthree⟩ : ∃ Δa ∈ leviComps R A A₀,
          ∃ Δb ∈ leviComps R A A₀, Δa ≠ Δb ∧ Δ₁ ≠ Δa ∧ Δ₁ ≠ Δb ∧
            ∀ Δ ∈ leviComps R A A₀, Δ = Δ₁ ∨ Δ = Δa ∨ Δ = Δb := by
        rcases hmem Δ₁ hΔ₁ with rfl | rfl | rfl
        · exact ⟨Y, hYm, Z, hZm, hYZ, hXY, hXZ, hmem⟩
        · exact ⟨X, hXm, Z, hZm, hXZ, Ne.symm hXY, hYZ,
            fun Δ hΔ => (hmem Δ hΔ).elim (fun e => Or.inr (Or.inl e))
              (fun e => e.elim Or.inl (fun e => Or.inr (Or.inr e)))⟩
        · exact ⟨X, hXm, Y, hYm, hXY, Ne.symm hXZ, Ne.symm hYZ,
            fun Δ hΔ => (hmem Δ hΔ).elim (fun e => Or.inr (Or.inl e))
              (fun e => e.elim (fun e => Or.inr (Or.inr e)) Or.inl)⟩
      obtain ⟨hBlk, hcl⟩ := union_block h hA hAne hA₀ hΔa hΔb
      refine hS₁ (hH8 (Δa ∪ Δb) ⟨hBlk, hcl⟩
        (fun B hB X hX => exists_mem_orbit_mem_lambdaSet h hA hAne hmax hA₀ hΔa hΔb hab hB hX)
        Δ₁ hΔ₁ (fun Y hY => notMem_union hΔ₁ hΔa hΔb h1a h1b hY) fun Δ hΔ hout => ?_)
      rcases hthree Δ hΔ with rfl | rfl | rfl
      · rfl
      · obtain ⟨Y, hY⟩ := nonempty_of_mem hΔ
        exact (hout Y hY (Or.inl hY)).elim
      · obtain ⟨Y, hY⟩ := nonempty_of_mem hΔ
        exact (hout Y hY (Or.inr hY)).elim
  ·
    exfalso
    have : Finite (leviComps R A A₀) := Nat.finite_of_card_ne_zero (by omega)
    set f : Fin 4 → leviComps R A A₀ := fun i => (Finite.equivFin _).symm (Fin.castLE h4 i)
    have hf : Function.Injective f :=
      (Finite.equivFin _).symm.injective.comp (Fin.castLE_injective h4)
    have hne : ∀ i j : Fin 4, i ≠ j → (f i : Set (Subgroup G)) ≠ f j := fun i j hij e =>
      hij (hf (Subtype.ext e))
    obtain ⟨hBlk, hcl⟩ := union_block h hA hAne hA₀ (f 0).2 (f 1).2
    have h3' : OrbitCollinear R A A₀ ((f 0 : Set (Subgroup G)) ∪ f 1) := fun B hB X hX =>
      exists_mem_orbit_mem_lambdaSet h hA hAne hmax hA₀ (f 0).2 (f 1).2 (hne 0 1 (by decide))
        hB hX
    have hout : ∀ i : Fin 4, i ≠ 0 → i ≠ 1 → ∀ Y ∈ (f i : Set (Subgroup G)),
        Y ∉ (f 0 : Set (Subgroup G)) ∪ f 1 := fun i hi0 hi1 Y hY =>
      notMem_union (f i).2 (f 0).2 (f 1).2 (hne i 0 hi0) (hne i 1 hi1) hY
    exact false_of_two_outside h hA hAne hmax hA₀ hBlk hcl h3' (f 2).2 (f 3).2
      (hne 2 3 (by decide)) (hout 2 (by decide) (by decide)) (hout 3 (by decide) (by decide))
      (hH6 _ ⟨hBlk, hcl⟩ h3' (f 2).1 (f 2).2 (hout 2 (by decide) (by decide)))

end Cases

end Sec9

end CFSG.Timmesfeld.ARS

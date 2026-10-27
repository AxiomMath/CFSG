module

public import CFSG.Timmesfeld.ARS.Sec9Block
public import CFSG.Timmesfeld.ARS.Sec9Two
public import CFSG.Timmesfeld.ARS.CaseD4

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

section SL2

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hmax hA₀

omit hmax in
theorem union_block {Δa Δb : Set (Subgroup G)} (hΔa : Δa ∈ leviComps R A A₀)
    (hΔb : Δb ∈ leviComps R A A₀) :
    Δa ∪ Δb ⊆ leviSet R A A₀ ∧ ∀ Y ∈ Δa ∪ Δb, comp R A A₀ Y ⊆ Δa ∪ Δb := by
  refine ⟨Set.union_subset (fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔa hY)
    (fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔb hY), fun Y hY => ?_⟩
  rcases hY with hY | hY
  · obtain ⟨E, -, rfl⟩ := hΔa
    rw [comp_eq_of_mem hY]
    exact Set.subset_union_left
  · obtain ⟨E, -, rfl⟩ := hΔb
    rw [comp_eq_of_mem hY]
    exact Set.subset_union_right

omit h hA hAne hmax hA₀ in
theorem notMem_union {Δ Δa Δb : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀)
    (hΔa : Δa ∈ leviComps R A A₀) (hΔb : Δb ∈ leviComps R A A₀) (ha : Δ ≠ Δa) (hb : Δ ≠ Δb)
    {Y : Subgroup G} (hY : Y ∈ Δ) : Y ∉ Δa ∪ Δb := by
  rintro (hYa | hYb)
  · obtain ⟨E, -, rfl⟩ := hΔ
    obtain ⟨F, -, rfl⟩ := hΔa
    exact ha (comp_eq_comp hY hYa)
  · obtain ⟨E, -, rfl⟩ := hΔ
    obtain ⟨F, -, rfl⟩ := hΔb
    exact hb (comp_eq_comp hY hYb)

theorem false_of_four {Δ Δa Δb Δc : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀)
    (hΔa : Δa ∈ leviComps R A A₀) (hΔb : Δb ∈ leviComps R A A₀) (hΔc : Δc ∈ leviComps R A A₀)
    (hab : Δa ≠ Δb) (hΔa' : Δ ≠ Δa) (hΔb' : Δ ≠ Δb) (hΔc' : Δ ≠ Δc) (hca : Δc ≠ Δa)
    (hcb : Δc ≠ Δb) (hS : IsSL2Comp Δ) : False := by
  obtain ⟨hBlk, hcl⟩ := union_block h hA hAne hA₀ hΔa hΔb
  exact false_of_two_outside h hA hAne hmax hA₀ hBlk hcl
    (fun B hB X hX => exists_mem_orbit_mem_lambdaSet h hA hAne hmax hA₀ hΔa hΔb hab hB hX) hΔ hΔc
    hΔc' (fun Y hY => notMem_union hΔ hΔa hΔb hΔa' hΔb' hY)
    (fun Y hY => notMem_union hΔc hΔa hΔb hca hcb hY)
    (fun E hE Z hZ hEZ => mem_lambdaSet_of_commuting h hA hAne hA₀ hmax hΔ hS hE hZ hEZ)

theorem false_of_four_le_card (h4 : 4 ≤ Nat.card (leviComps R A A₀)) {Δ : Set (Subgroup G)}
    (hΔ : Δ ∈ leviComps R A A₀) (hS : IsSL2Comp Δ) : False := by
  have : Finite (leviComps R A A₀) := Nat.finite_of_card_ne_zero (by omega)
  set f : Fin 4 → leviComps R A A₀ := fun i => (Finite.equivFin _).symm (Fin.castLE h4 i)
  have hf : Function.Injective f :=
    (Finite.equivFin _).symm.injective.comp (Fin.castLE_injective h4)
  have hne : ∀ i j : Fin 4, i ≠ j → (f i : Set (Subgroup G)) ≠ f j := fun i j hij e =>
    hij (hf (Subtype.ext e))
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ : ∃ a b c : Fin 4, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      Δ ≠ f a ∧ Δ ≠ f b ∧ Δ ≠ f c := by
    by_cases h0 : Δ = f 0
    · refine ⟨1, 2, 3, by decide, by decide, by decide, ?_, ?_, ?_⟩ <;> rw [h0] <;>
        exact hne _ _ (by decide)
    by_cases h1 : Δ = f 1
    · refine ⟨0, 2, 3, by decide, by decide, by decide, h0, ?_, ?_⟩ <;> rw [h1] <;>
        exact hne _ _ (by decide)
    by_cases h2 : Δ = f 2
    · refine ⟨0, 1, 3, by decide, by decide, by decide, h0, h1, ?_⟩
      rw [h2]
      exact hne _ _ (by decide)
    exact ⟨0, 1, 2, by decide, by decide, by decide, h0, h1, h2⟩
  exact false_of_four h hA hAne hmax hA₀ hΔ (f a).2 (f b).2 (f c).2 (hne a b hab) ha hb hc
    (hne c a (Ne.symm hac)) (hne c b (Ne.symm hbc)) hS

theorem card_leviComps_eq_three (hr : 1 < Nat.card (leviComps R A A₀))
    (hall : ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ) : Nat.card (leviComps R A A₀) = 3 := by
  have h2 : Nat.card (leviComps R A A₀) ≠ 2 := fun h2 =>
    false_of_card_two h hA hAne hmax hA₀ hall h2
  have h4 : Nat.card (leviComps R A A₀) < 4 := by
    by_contra h4
    have : Finite (leviComps R A A₀) := Nat.finite_of_card_ne_zero (by omega)
    obtain ⟨Δ⟩ := (Nat.card_pos_iff.1 (by omega : 0 < Nat.card (leviComps R A A₀))).1
    exact false_of_four_le_card h hA hAne hmax hA₀ (by omega) Δ.2 (hall Δ Δ.2)
  omega

omit hmax in
theorem exists_leviSL2Cube (h3 : Nat.card (leviComps R A A₀) = 3)
    (hall : ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ) :
    ∃ P Q : Fin 3 → Subgroup G, LeviSL2Cube R A A₀ P Q := by
  obtain ⟨P, Q, hPQ, -⟩ := leviSL2Family_of_forall h hA hAne hA₀ hall
  have : Finite (leviComps R A A₀) := Nat.finite_of_card_ne_zero (by omega)
  have e : Fin 3 ≃ leviComps R A A₀ := (h3 ▸ (Finite.equivFin (leviComps R A A₀)).symm :)
  exact ⟨P ∘ e, Q ∘ e, hPQ.comp_equiv e⟩

end SL2

theorem lieModel_of_forall_isSL2Comp {G : Type} [Group G] {R : Set (Subgroup G)} (h : Hyp G R)
    {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hr : 1 < Nat.card (leviComps R A A₀)) (hall : ∀ Δ ∈ leviComps R A A₀, IsSL2Comp Δ) :
    ∃ f : ℕ, 1 ≤ f ∧ (∀ E ∈ R, Nat.card E = 2 ^ f) ∧
      Blueprint.LieModel G .POmegaPlus 4 2 f := by
  obtain ⟨P, Q, hPQ⟩ := exists_leviSL2Cube h hA hAne hA₀
    (card_leviComps_eq_three h hA hAne hmax hA₀ hr hall) hall
  exact lieModel_caseD4 h hA hAne hmax hA₀ hPQ

end Sec9

end CFSG.Timmesfeld.ARS

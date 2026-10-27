module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructA
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec7.StructB

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem exists_isRegFam_inf_eq_zpowers
    (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A)
    (hT : TypeA p A θ ∨ ∃ E K : Subgroup G, TypeBCore p A θ E K ∧ ¬ E ≤ B) :
    ∀ a ∈ B, a ≠ 1 → ∃ (Ω : Set (Subgroup G)) (N : Subgroup G),
      IsRegFam A (θ a) Ω N ∧ B ⊓ N = Subgroup.zpowers a := by
  intro a haB ha1
  have haA : a ∈ A := hB.1 haB
  have hF : Subgroup.zpowers a ∈ signalizerFunctorEk p 1 A := h.zpowers_mem_E1 haA ha1
  have hFB : Subgroup.zpowers a ≤ B := Subgroup.zpowers_le.mpr haB
  rcases hT with hA | ⟨E, K, hE, hEB⟩
  · refine ⟨lcal (θ a), Subgroup.zpowers a, ?_, inf_eq_right.mpr hFB⟩
    have := isRegFam_line_of_typeA h hA hF
    rwa [h.isFunctor.thetaOf_zpowers haA ha1] at this
  · have hFE : Subgroup.zpowers a ≠ E := fun hEq => hEB (hEq ▸ hFB)
    refine ⟨lcal (θ a), E ⊔ Subgroup.zpowers a, ?_, ?_⟩
    · have := isRegFam_line_of_typeB h hE hF hFE
      rwa [h.isFunctor.thetaOf_zpowers haA ha1] at this
    · have hplane : E ⊔ Subgroup.zpowers a ∈ signalizerFunctorEk p 2 A :=
        h.sup_mem_E2_of_ne hE.mem hF fun hEF => hFE hEF.symm
      have hne : B ≠ E ⊔ Subgroup.zpowers a := fun hEq => hEB (hEq ▸ le_sup_left)
      have hline := h.inf_mem_E1_of_ne_E2 hB hplane hne
      exact (Subgroup.eq_of_le_of_card_ge (le_inf hFB le_sup_right)
        (by rw [hline.2, hF.2])).symm

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

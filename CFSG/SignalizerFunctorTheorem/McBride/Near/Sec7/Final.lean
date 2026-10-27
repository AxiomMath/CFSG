module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAuxBridge
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec7.FinalAux5

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thm71
    (h : Counterexample p A θ) {E B : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hEs : Group.IsSolvable (thetaOf θ E))
    (hB : B ∈ signalizerFunctorEk p 2 A) (hEB : E ≤ B) :
    ∃ W : Fin p → Subgroup G, Function.Injective W ∧ IsDirectProduct (Set.range W) (wsub p A θ) ∧
      (∀ a ∈ A, ∀ i, ∃ j, (W i).map (MulAut.conj a).toMonoidHom = W j) ∧
      (∀ i j, ∃ a ∈ A, (W i).map (MulAut.conj a).toMonoidHom = W j) ∧
      (∀ i, A ⊓ Subgroup.normalizer (W i : Set G) = B) ∧
      ∀ b ∈ B, b ∉ E →
        IsDirectProduct (Set.range fun i => W i ⊓ kOf (θ b)) (kOf (θ b)) := by
  have D := Sec7S35.Data.mk' h hE hEs
  obtain ⟨V, r, hV⟩ := Sec7S35.VData.exists h hE hEs
  exact Sec7S35.thm71_of_data D ⟨hE, hB, hEB⟩ hV

theorem false
    (h : Counterexample p A θ) : False := by
  obtain ⟨E, hE, -, -, -, -, hEs, -⟩ := h.thm61
  have D := Sec7S35.Data.mk' h hE hEs
  refine Sec7S35.false_of_thm71 h D fun {B} hB hEB => ?_
  obtain ⟨W, h1, h2, h3, h4, h5, h6⟩ := thm71 h hE hEs hB hEB
  exact ⟨W, ⟨h1, h2, h3, h4, h5, h6⟩⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Near

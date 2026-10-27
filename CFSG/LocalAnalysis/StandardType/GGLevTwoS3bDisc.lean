module

public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

public section

namespace CFSG.StandardType.LevTwo

theorem levTwoS3d_not_irred_of_side {α : Type} (P S : Set α) (r : α → α → Prop)
    (hSP : S ⊆ P) (hne : ∃ x, x ∈ S) (hnall : ∃ y, y ∈ P ∧ y ∉ S)
    (hinv : ∀ a b, a ∈ S → b ∈ P → r a b → b ∈ S) :
    ¬ ∀ a ∈ P, ∀ b ∈ P, Relation.ReflTransGen (fun x y => y ∈ P ∧ r x y) a b := by
  intro h
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hbP, hbS⟩ := hnall
  have hchain := h a (hSP ha) b hbP
  have : ∀ c, Relation.ReflTransGen (fun x y => y ∈ P ∧ r x y) a c → c ∈ S := by
    intro c hc
    induction hc with
    | refl => exact ha
    | tail _ hbc ih => exact hinv _ _ ih hbc.1 hbc.2
  exact hbS (this b hchain)

theorem levTwoS3d_card_le_two_of_span {ι : Type} [Fintype ι] (s : Finset (ι → ℤ)) (u v : ι → ℚ)
    (hspan : ∀ x ∈ s, (fun i => ((x i : ℤ) : ℚ)) ∈ Submodule.span ℚ {u, v})
    (hli : LinearIndependent ℚ (fun x : s => (fun i => (((x : ι → ℤ) i : ℤ) : ℚ)))) :
    s.card ≤ 2 := by
  classical
  let W : Submodule ℚ (ι → ℚ) := Submodule.span ℚ {u, v}
  have hmem : ∀ x : s, (fun i => (((x : ι → ℤ) i : ℤ) : ℚ)) ∈ W := fun x => hspan x x.2
  have hli' : LinearIndependent ℚ
      (fun x : s => (⟨(fun i => (((x : ι → ℤ) i : ℤ) : ℚ)), hmem x⟩ : W)) := by
    apply LinearIndependent.of_comp W.subtype
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  have hfin : Module.finrank ℚ W ≤ 2 := by
    have h1 := finrank_span_finset_le_card (R := ℚ) ({u, v} : Finset (ι → ℚ))
    have h2 : (({u, v} : Finset (ι → ℚ)) : Set (ι → ℚ)) = {u, v} := by simp
    rw [h2] at h1
    exact h1.trans Finset.card_le_two
  simpa using hcard.trans hfin

end CFSG.StandardType.LevTwo

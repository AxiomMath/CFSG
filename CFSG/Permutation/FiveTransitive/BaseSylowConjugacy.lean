module

public import CFSG.Permutation.FiveTransitive.StabilizerSylowConjugacy
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.BaseSylowConjugacy

open MulAction

theorem exists_embedding_range
    (X : Type*) [Fintype X] (k : ℕ) (s : Set X) (hs : s.ncard = k) :
    ∃ e : Fin k ↪ X, Set.range e = s := by
  classical
  let _ : Fintype s := Fintype.ofFinite _
  let e₀ : s ≃ Fin k := Fintype.equivFinOfCardEq
    (by simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hs)
  let e : Fin k ↪ X := e₀.symm.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (e₀.symm i).property
  · intro hx
    refine ⟨e₀ ⟨x, hx⟩, ?_⟩
    change (e₀.symm (e₀ ⟨x, hx⟩)).val = x
    simp

theorem fixing_range_eq_stabilizer
    (G X : Type*) [Group G] [MulAction G X] {k : ℕ} (e : Fin k ↪ X) :
    fixingSubgroup G (Set.range e) = stabilizer G e := by
  ext g
  rw [mem_fixingSubgroup_iff, mem_stabilizer_iff]
  constructor
  · intro h
    ext i
    exact h (e i) ⟨i, rfl⟩
  · intro h
    rintro _ ⟨i, rfl⟩
    exact congrArg (fun f : Fin k ↪ X => f i) h

private theorem exists_of_eq_stabilizer
    {G Y : Type*} [Group G] [Finite G] [MulAction G Y]
    {p : ℕ} [Fact p.Prime] (x y : Y) (hxy : ∃ a : G, a • x = y)
    (H K : Subgroup G) (hH : H = stabilizer G x) (hK : K = stabilizer G y)
    (S : Sylow p H) (T : Sylow p K) :
    ∃ a : G, ((S : Subgroup H).map H.subtype).map (MulAut.conj a).toMonoidHom =
      (T : Subgroup K).map K.subtype := by
  subst H
  subst K
  obtain ⟨a, _, ha⟩ := StabilizerSylowConjugacy.exists_conjugating_transporter x y hxy S T
  exact ⟨a, ha⟩

theorem exists_conjugate_sylow_images
    (G X : Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : IsMultiplyPretransitive G X k)
    (s t : Set X) (hs : s.ncard = k) (ht : t.ncard = k)
    {p : ℕ} [Fact p.Prime]
    (S : Sylow p (fixingSubgroup G s)) (T : Sylow p (fixingSubgroup G t)) :
    ∃ a : G,
      ((S : Subgroup (fixingSubgroup G s)).map (fixingSubgroup G s).subtype).map
        (MulAut.conj a).toMonoidHom =
      (T : Subgroup (fixingSubgroup G t)).map (fixingSubgroup G t).subtype := by
  obtain ⟨e, he⟩ := exists_embedding_range X k s hs
  obtain ⟨f, hf⟩ := exists_embedding_range X k t ht
  apply exists_of_eq_stabilizer e f (isMultiplyPretransitive_iff.mp hk e f)
    (fixingSubgroup G s) (fixingSubgroup G t) _ _ S T
  · rw [← he, fixing_range_eq_stabilizer]
  · rw [← hf, fixing_range_eq_stabilizer]

end FiveTransitive.BaseSylowConjugacy

end CFSG

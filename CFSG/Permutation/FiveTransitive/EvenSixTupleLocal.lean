module

public import CFSG.Permutation.FiveTransitive.SixLocalSylowExponentTwo
public import CFSG.Permutation.FiveTransitive.StabilizerSylowConjugacy
public import CFSG.Permutation.FiveTransitive.ConjugateFixedNormalizer
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.EvenSixTupleLocal

open MulAction FixedSetNormalizerPerm

@[expose] def EvenFixed (G X:Type*) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (A:Subgroup G) : Prop :=
  letI := Fintype.ofFinite (fixedPoints A X)
  letI := Classical.decEq (fixedPoints A X)
  ∀n:G,∀hn:n∈Subgroup.normalizer (A:Set G),(fixedPerm G X A n hn).sign=1

@[expose] def Property (G X:Type*) [Group G] [Finite G] [Fintype X] [MulAction G X] : Prop :=
  ∀(a:Fin 4 ↪ X)(P:Sylow 2 (stabilizer G a)),
    let A := (P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype
    Nat.card (fixedPoints A X)=6 ∧ EvenFixed G X A

theorem fixing_range {G X:Type*} [Group G] [MulAction G X]
    {k:ℕ} (a:Fin k ↪ X) : fixingSubgroup G (Set.range a)=stabilizer G a := by
  ext g
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro h
    apply Function.Embedding.ext
    intro i
    exact h (a i) ⟨i,rfl⟩
  · intro h x hx
    obtain ⟨i,rfl⟩ := hx
    exact DFunLike.congr_fun h i

theorem to_set_property
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h:Property G X) : SixLocalSylowExponentTwo.EvenSixLocal G X := by
  classical
  intro s hs S
  have hcard:Nat.card s=4 := by rwa [Nat.card_coe_set_eq]
  let E:s ≃ Fin 4 := Finite.equivFinOfCardEq hcard
  let a:Fin 4 ↪ X := E.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hra:Set.range a=s := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact (E.symm i).property
    · intro hx
      exact ⟨E ⟨x,hx⟩,congrArg Subtype.val (E.symm_apply_apply ⟨x,hx⟩)⟩
  have hK:fixingSubgroup G s=stabilizer G a := by rw [←hra,fixing_range]
  have ha := h a
  rw [←hK] at ha
  obtain ⟨hc,he⟩ := ha S
  exact ⟨by rwa [←Nat.card_coe_set_eq],he⟩

theorem of_base
    {G X:Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (h4:IsMultiplyPretransitive G X 4) (a:Fin 4 ↪ X)
    (P:Sylow 2 (stabilizer G a))
    (hcard:Nat.card (fixedPoints
      ((P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype) X)=6)
    (heven:let A := (P:Subgroup (stabilizer G a)).map (stabilizer G a).subtype
      ∀n:G,∀hn:n∈Subgroup.normalizer (A:Set G),
      letI := Fintype.ofFinite (fixedPoints A X)
      letI := Classical.decEq (fixedPoints A X)
      (fixedPerm G X A n hn).sign=1) : Property G X := by
  intro b S
  obtain ⟨g,_,hg⟩ := StabilizerSylowConjugacy.exists_conjugating_transporter
    a b (h4.exists_smul_eq a b) P S
  obtain ⟨hc,he⟩ := ConjugateFixedNormalizer.six_even_of_conjugate G X _ _ g hg
    (by rwa [←Nat.card_coe_set_eq]) heven
  exact ⟨by rwa [Nat.card_coe_set_eq],he⟩

end FiveTransitive.EvenSixTupleLocal

end CFSG

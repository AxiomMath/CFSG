module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree68LargePrimeFixed

open MulAction SylowFixedActionCore

theorem bounds_and_transitive
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow p (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    5 ≤ Nat.card (sylowFixedPoints X P s S) ∧
      Nat.card (sylowFixedPoints X P s S) ≤ 34 ∧
      IsMultiplyPretransitive (sylowNormalizer X P s S) (sylowFixedPoints X P s S) 5 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective
    (fixingSubgroup P s).subtype_injective
  have hQne : Q ≠ ⊥ := by intro he; apply hS; rw [← hQcard,he]; simp
  have hupper := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hQne
  rw [← FixedNormalizerAction.fixed_eq Q,hcard] at hupper
  have hlower := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hlower
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  refine ⟨hlower,hupper,?_⟩
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
  refine ⟨g,?_⟩
  apply Function.Embedding.ext
  intro i
  exact hg i

end FiveTransitive.Degree68LargePrimeFixed

end CFSG

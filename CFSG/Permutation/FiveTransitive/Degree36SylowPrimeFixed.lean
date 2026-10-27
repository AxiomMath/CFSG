module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree36SylowPrimeFixed

open MulAction SylowFixedActionCore

theorem bounds_and_alternating
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 7 ∨ p = 11 ∨ p = 13)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow p (fixingSubgroup P s)) [Fintype (sylowFixedPoints X P s S)]
    (hS : Nat.card S ≠ 1) :
    8 ≤ Nat.card (sylowFixedPoints X P s S) ∧
      Nat.card (sylowFixedPoints X P s S) ≤ 18 ∧
      alternatingGroup (sylowFixedPoints X P s S) ≤
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hQne : Q ≠ ⊥ := by intro he; apply hS; rw [← hQcard,he]; simp
  have hfixeq : (F : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx q
      exact hx (⟨⟨q.val,Q.le_normalizer q.property⟩,q.property⟩ : sylowInNormalizer X P s S)
    · intro hx q
      exact hx (⟨q.val.val,q.property⟩ : Q)
  have hupper := MinimalOrbitFixedBounds.fixed_card_le_half X P (by omega) h5 hnotAlt Q hQne
  rw [← hfixeq,hcard] at hupper
  have hlower := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hlower
  change 5 ≤ Nat.card F at hlower
  have hmod := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % p = Nat.card F % p at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have height : 8 ≤ Nat.card F := by rcases hcases with rfl | rfl | rfl <;> omega
  have hnot12 : Nat.card F ≠ 12 := by rcases hcases with rfl | rfl | rfl <;> omega
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  let J := (toPermHom N F).range
  have hAlt : alternatingGroup F ≤ J := by
    apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu
      F J
    · rw [← Nat.card_eq_fintype_card]; exact hlower
    · rw [← Nat.card_eq_fintype_card]; omega
    · rw [← Nat.card_eq_fintype_card]; omega
    · rw [← Nat.card_eq_fintype_card]; omega
    · intro a b ha hb
      obtain ⟨g,hg⟩ := hN5 a b ha hb
      exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩
  exact ⟨height,hupper,hAlt⟩

end FiveTransitive.Degree36SylowPrimeFixed

end CFSG

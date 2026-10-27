module

public import CFSG.Permutation.FiveTransitive.Degree39ThreeFixedCases
public import CFSG.Permutation.FiveTransitive.Degree39ThreeBound
public import CFSG.Permutation.FiveTransitive.Degree39ThreeGroupTwelveExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree39SylowThreeEntrance

open MulAction SylowFixedActionCore

theorem three_fixed_card_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 6 ∧
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hNtrans : IsMultiplyPretransitive N F 5 :=
    FiveTransitive.isMultiplyPretransitive_of_explicit N F 5 hN5
  have hF : Nat.card F = 6 := by
    rcases Degree39ThreeFixedCases.three_fixed_card_cases P hcard h5 hnotAlt s hs S hS with h | h
    · exact h
    · exact (Degree39ThreeGroupTwelveExclusion.false_of_five_transitive
        P hcard h5 hnotAlt Q (S.isPGroup'.map (fixingSubgroup P s).subtype) h hNtrans).elim
  refine ⟨hF,?_⟩
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  change IsMultiplyPretransitive (toPermHom N F).range F (Nat.card F - 1)
  rw [hF]
  exact FiveTransitive.isMultiplyPretransitive_range_toPermHom N F 5 hNtrans

theorem three_entrance
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 6 ∧
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = ⊤ ∧
      Nat.card S ≤ 2187 := by
  have hF := three_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  have hQbound := Degree39ThreeBound.three_card_le_2187
    P hcard h5 hnotAlt Q (S.isPGroup'.map (fixingSubgroup P s).subtype)
    (by rw [← hfixeq,hF.1])
  exact ⟨hF.1,hF.2,by rwa [hQcard] at hQbound⟩

end FiveTransitive.Degree39SylowThreeEntrance

end CFSG

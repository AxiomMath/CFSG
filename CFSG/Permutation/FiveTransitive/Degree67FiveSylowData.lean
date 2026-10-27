module

public import CFSG.Permutation.FiveTransitive.Degree67FiveFixedCases
public import CFSG.Permutation.FiveTransitive.Degree67FiveSevenObstruction

public section

namespace CFSG

namespace FiveTransitive.Degree67FiveSylowData

open MulAction Subgroup SylowFixedActionCore

private theorem alternating_image_of_fixed_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (_hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (_hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hF7 : Nat.card (sylowFixedPoints X P s S) = 7) :
    let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
    alternatingGroup (sylowFixedPoints X P s S) ≤
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = 7 := hF7
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  let J := (toPermHom N F).range
  change alternatingGroup F ≤ J
  apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F J
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · rw [← Nat.card_eq_fintype_card,hF]; norm_num
  · intro a b ha hb
    obtain ⟨g,hg⟩ := hN5 a b ha hb
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩

theorem fixed_card_eq_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 12 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases Degree67FiveFixedCases.five_fixed_card_cases P hcard h5 hnotAlt s hs S hS with hF | hF
  · let Q := sylowImage X P s S
    let _ : Fintype (FixedNormalizerAction.Fixed (X := X) Q) := Fintype.ofFinite _
    have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
    have hAlt := alternating_image_of_fixed_seven P hcard h5 hnotAlt s hs S hF
    exact (Degree67FiveSevenObstruction.excluded P hcard hseven Q hQ hF hAlt).elim
  · exact hF

end FiveTransitive.Degree67FiveSylowData

end CFSG

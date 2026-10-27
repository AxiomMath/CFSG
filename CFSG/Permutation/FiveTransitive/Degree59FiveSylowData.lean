module

public import CFSG.Permutation.FiveTransitive.Degree59FiveFixedCases
public import CFSG.Permutation.FiveTransitive.Degree59FiveTwentyFour

public section

namespace CFSG

namespace FiveTransitive.Degree59FiveSylowData

open MulAction Subgroup SylowFixedActionCore

theorem five_fixed_card_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 59)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
    Nat.card (sylowFixedPoints X P s S) = 9 ∧
      alternatingGroup (sylowFixedPoints X P s S) ≤
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hF : Nat.card F = 9 :=
    (Degree59FiveFixedCases.five_fixed_card_cases P hcard h5 hnotAlt s hs S hS).resolve_right
      (Degree59FiveTwentyFour.fixed_ne_twentyFour P hcard h5 hnotAlt s hs S)
  refine ⟨hF,?_⟩
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

end FiveTransitive.Degree59FiveSylowData

end CFSG

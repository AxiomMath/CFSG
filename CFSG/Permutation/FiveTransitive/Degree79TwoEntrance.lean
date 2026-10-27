module

public import CFSG.Permutation.FiveTransitive.SylowTwoFixedDegreeBounded
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoEntrance

open MulAction SylowFixedActionCore

theorem fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) = 5 ∨
      Nat.card (sylowFixedPoints X P s S) = 7 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hlo := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hlo
  have hb := SylowTwoFixedDegreeBounded.fixed_degree_le_eight_or_eq_twelve X P h5 s hs S
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % 2 = Nat.card (sylowFixedPoints X P s S) % 2 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  omega

theorem alternating_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
    alternatingGroup (sylowFixedPoints X P s S) ≤
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite _
  have hc := fixed_card_cases P hcard h5 s hs S
  change Nat.card F = 5 ∨ Nat.card F = 7 at hc
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F
  · rw [← Nat.card_eq_fintype_card]; omega
  · rw [← Nat.card_eq_fintype_card]; omega
  · rw [← Nat.card_eq_fintype_card]; omega
  · rw [← Nat.card_eq_fintype_card]; omega
  · intro a b ha hb
    obtain ⟨g,hg⟩ := hN5 a b ha hb
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩

end FiveTransitive.Degree79TwoEntrance

end CFSG

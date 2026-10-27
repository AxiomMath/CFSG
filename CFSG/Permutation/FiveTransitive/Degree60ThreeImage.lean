module

public import CFSG.Permutation.FiveTransitive.FixedActionGoursat
public import CFSG.Permutation.FiveTransitive.Helpers
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.Degree60ThreeImage

open MulAction SylowFixedActionCore

theorem card_eq_95040
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (_hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (_hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hF12 : Nat.card (sylowFixedPoints X P s S) = 12) :
    Nat.card (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = 95040 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let J := (toPermHom N F).range
  let _ : Fintype J := Fintype.ofFinite J
  have hF : Fintype.card F = 12 := by
    rw [← Nat.card_eq_fintype_card]
    exact hF12
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hclass := Helpers.classification_of_five_transitive_of_card_eq_twelve J F hF (by
    intro a b ha hb
    obtain ⟨g,hg⟩ := hN5 a b ha hb
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩)
  have haltfalse (horders : Nat.card J = (Fintype.card F).factorial ∨
      Nat.card J = (Fintype.card F).factorial / 2) : False := by
    have hAlt := FiveTransitive.FixedActionGoursat.alternatingGroup_le_of_card_eq_factorial_or_half
      F J (by rw [hF]; norm_num) horders
    have hb := (fixed_card_bound_of_alternating_normalizer_action X P s hs S hAlt).2
      (by norm_num : 3 ≠ 2)
    change Fintype.card F - 5 < 3 at hb
    rw [hF] at hb
    omega
  change Nat.card J = 95040
  rcases hclass with hsym | halt | hm
  · exact (haltfalse (Or.inl (by simpa only [Nat.card_eq_fintype_card] using hsym))).elim
  · exact (haltfalse (Or.inr (by simpa only [Nat.card_eq_fintype_card] using halt.2))).elim
  · simpa only [Nat.card_eq_fintype_card] using hm.2

end FiveTransitive.Degree60ThreeImage

end CFSG

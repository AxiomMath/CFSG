module

public import CFSG.Permutation.FiveTransitive.Degree69ThreeTwelveExclusion
public import CFSG.Permutation.FiveTransitive.Degree69SevenFree
public import CFSG.Permutation.FiveTransitive.Degree69ThreeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree69ThreeSix

open MulAction SylowFixedActionCore

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 6 := by
  rcases Degree69ThreeFixed.three_fixed_card_cases P hcard h5 hnotAlt s hs S hS with h6 | h12
  · exact h6
  · exact (Degree69ThreeTwelveExclusion.not_fixed_twelve P hcard h5 hnotAlt
      (Degree69SevenFree.not_dvd_ambient P hcard h5 hnotAlt) s hs S h12).elim

theorem fixed_card_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 6 ∧
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = ⊤ := by
  classical
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hF := fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 6 at hF
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  let J := (toPermHom N F).range
  have hJ5 : IsMultiplyPretransitive J F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,DFunLike.ext _ _ hg⟩
  refine ⟨hF,?_⟩
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  change IsMultiplyPretransitive J F (Nat.card F - 1)
  let _ := hJ5
  exact isMultiplyPretransitive_of_le (G := J) (α := F) (n := 5)
    (by rw [hF]) (by rw [hF]; omega)

end FiveTransitive.Degree69ThreeSix

end CFSG

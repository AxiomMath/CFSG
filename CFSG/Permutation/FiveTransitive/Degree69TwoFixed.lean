module

public import CFSG.Permutation.FiveTransitive.SylowTwoFixedDegreeBounded
public import CFSG.Permutation.FiveTransitive.Degree69SevenFree

public section

namespace CFSG

namespace FiveTransitive.Degree69TwoFixed

open MulAction Subgroup FixedNormalizerAction SylowFixedActionCore

theorem fixed_five_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) = 5 ∧
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hbase := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hbase
  change 5 ≤ Nat.card F at hbase
  have hb := SylowTwoFixedDegreeBounded.fixed_degree_le_eight_or_eq_twelve X P h5 s hs S
  change Nat.card F ≤ 8 ∨ Nat.card F = 12 at hb
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % 2 = Nat.card F % 2 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hNexp := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hN5 : IsMultiplyPretransitive N F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hNexp a b a.injective b.injective
    exact ⟨g,DFunLike.ext _ _ hg⟩
  let b : Fin 5 ↪ F := (Fin.castLEEmb hbase).trans (Finite.equivFin F).symm.toEmbedding
  let t : Set F := Set.range b
  have ht : t.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have htrans : IsMultiplyPretransitive N F t.ncard := by rw [ht]; exact hN5
  have hi := htrans.index_of_fixingSubgroup_eq t
  have hnot7 : Nat.card F ≠ 7 := by
    intro hF
    have hd : 7 ∣ (fixingSubgroup N t).index := by
      rw [hi, ht, hF]
      norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial]
    exact Degree69SevenFree.not_dvd_ambient P hcard h5 hnotAlt
      ((hd.trans (fixingSubgroup N t).index_dvd_card).trans (Subgroup.card_subgroup_dvd_card N))
  have hF : Nat.card F = 5 := by omega
  refine ⟨hF,?_⟩
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  change IsMultiplyPretransitive rho.range F (Nat.card F - 1)
  rw [hF]
  change IsMultiplyPretransitive rho.range F 4
  let _ : IsMultiplyPretransitive N F 5 := hN5
  have hN4 : IsMultiplyPretransitive N F 4 :=
    isMultiplyPretransitive_of_le (G := N) (α := F) (n := 5) (by decide) hbase
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g,hg⟩ := hN4.exists_smul_eq a b
  exact ⟨⟨rho g,⟨g,rfl⟩⟩,hg⟩

end FiveTransitive.Degree69TwoFixed

end CFSG

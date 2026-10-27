module

public import CFSG.Permutation.FiveTransitive.Degree54TwoAmbientEleven

public section

namespace CFSG

namespace FiveTransitive.Degree54ThreeFixed

open MulAction SylowFixedActionCore

theorem fixed_card_eq_six
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 6 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
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
  change Nat.card X % 3 = Nat.card F % 3 at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hNmt : IsMultiplyPretransitive N F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
    exact ⟨g,DFunLike.ext _ _ hg⟩
  let b : Fin 5 ↪ F := (Fin.castLEEmb hlower).trans (Finite.equivFin F).symm.toEmbedding
  let t : Set F := Set.range b
  have ht : t.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have htrans : IsMultiplyPretransitive N F t.ncard := by rw [ht]; exact hNmt
  have hi := htrans.index_of_fixingSubgroup_eq t
  have hnotMathieu : Nat.card F ≠ 12 ∧ Nat.card F ≠ 24 := by
    have hf (hF : Nat.card F = 12 ∨ Nat.card F = 24) : False := by
      have hd : 11 ∣ (fixingSubgroup N t).index := by
        rw [hi,ht]
        rcases hF with hF | hF <;> rw [hF] <;>
          norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial]
      exact Degree54TwoAmbientEleven.eleven_not_dvd_card P hcard h5 hnotAlt
        ((hd.trans (fixingSubgroup N t).index_dvd_card).trans (Subgroup.card_subgroup_dvd_card N))
    exact ⟨fun h => hf (Or.inl h),fun h => hf (Or.inr h)⟩
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
  have hb := (fixed_card_bound_of_alternating_normalizer_action X P s hs S hAlt).2
    (by norm_num : 3 ≠ 2)
  change Fintype.card F - 5 < 3 at hb
  rw [← Nat.card_eq_fintype_card] at hb
  change Nat.card F = 6
  omega

theorem fixed_card_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
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

end FiveTransitive.Degree54ThreeFixed

end CFSG

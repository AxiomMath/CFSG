module

public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction
public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleClassification

public section

namespace CFSG

namespace FiveTransitive.Degree72SevenFixed

open MulAction SylowFixedActionCore

theorem fixed_card_and_alternating
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
    Nat.card (sylowFixedPoints X P s S) = 9 ∧
      alternatingGroup (sylowFixedPoints X P s S) ≤
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
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
  change Nat.card X % 7 = Nat.card F % 7 at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
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
  have hAlt : alternatingGroup F ≤ J := by
    by_cases h30 : Nat.card F = 30
    · exact TwoPrimeCycleClassification.alternatingGroup_le 13 4 (by decide) (by decide) (Or.inr rfl) J
        (by rw [← Nat.card_eq_fintype_card,h30]) hJ5
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
    (by norm_num : 7 ≠ 2)
  change Fintype.card F - 5 < 7 at hb
  rw [← Nat.card_eq_fintype_card] at hb
  have hF : Nat.card F = 9 := by omega
  exact ⟨hF,hAlt⟩

end FiveTransitive.Degree72SevenFixed

end CFSG

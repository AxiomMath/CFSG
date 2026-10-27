module

public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds
public import CFSG.Permutation.FiveTransitive.SylowFixedActionPrimeFree
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree67ElevenFixed

open MulAction SylowFixedActionCore

theorem fixed_card_eq_twelve
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 12 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
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
  change Nat.card X % 11 = Nat.card F % 11 at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  let J := (toPermHom N F).range
  by_contra hF12
  change Nat.card F ≠ 12 at hF12
  have hF23 : Nat.card F = 23 := by omega
  have hAlt : alternatingGroup F ≤ J := by
    apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F J
    · rw [← Nat.card_eq_fintype_card]; exact hlower
    · rw [← Nat.card_eq_fintype_card,hF23]; omega
    · rw [← Nat.card_eq_fintype_card,hF23]; omega
    · rw [← Nat.card_eq_fintype_card,hF23]; omega
    · intro a b ha hb
      obtain ⟨g,hg⟩ := hN5 a b ha hb
      exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩
  have hb := (fixed_card_bound_of_alternating_normalizer_action X P s hs S hAlt).2
    (by norm_num : 11 ≠ 2)
  change Fintype.card F - 5 < 11 at hb
  rw [← Nat.card_eq_fintype_card,hF23] at hb
  omega

theorem card_le_one_twenty_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) : Nat.card S ≤ 121 := by
  classical
  by_cases hS : Nat.card S = 1
  · omega
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 11 Q := S.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective
    (fixingSubgroup P s).subtype_injective
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx q
      exact hx (⟨⟨q.val,Q.le_normalizer q.property⟩,q.property⟩ : sylowInNormalizer X P s S)
    · intro hx q
      exact hx (⟨q.val.val,q.property⟩ : Q)
  have hfixed : Nat.card (fixedPoints Q X) = 12 := by
    rw [← hfixeq]
    exact fixed_card_eq_twelve P hcard h5 hnotAlt s hs S hS
  have htuple := Degree67LargePrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    22 (by rw [hfixed])
  rw [hfixed] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he2 : e ≤ 2 := by
    by_contra hn
    have hpow : 11 ^ 3 ∣ Nat.card Q := by
      rw [he]
      exact pow_dvd_pow 11 (by omega : 3 ≤ e)
    have hc := hpow.trans htuple
    norm_num at hc
  rw [← hQcard,he]
  exact Nat.pow_le_pow_right (by decide : 0 < 11) he2

end FiveTransitive.Degree67ElevenFixed

end CFSG

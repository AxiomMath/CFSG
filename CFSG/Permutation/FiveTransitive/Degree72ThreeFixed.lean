module

public import CFSG.Permutation.FiveTransitive.TwoPrimeCycleClassification
public import CFSG.Permutation.FiveTransitive.PrimePredFour
public import CFSG.Permutation.FiveTransitive.Degree36Classification

public section

namespace CFSG

namespace FiveTransitive.Degree72ThreeFixed

open MulAction SylowFixedActionCore

theorem three_fixed_card_cases
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 6 ∨ Nat.card (sylowFixedPoints X P s S) = 12 := by
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
  let J := (toPermHom N F).range
  by_cases hF12 : Nat.card F = 12
  · exact Or.inr hF12
  have hF24 : Nat.card F ≠ 24 := by
    intro hf24
    let _ : Fintype J := Fintype.ofFinite J
    have hJ5 : IsMultiplyPretransitive J F 5 := by
      constructor
      intro a b
      obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
      exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,DFunLike.ext _ _ hg⟩
    have hclass := Degree24.card_classification_of_five_transitive J F
      (by rwa [← Nat.card_eq_fintype_card]) (by
        intro a b ha hb
        obtain ⟨g,hg⟩ := hN5 a b ha hb
        exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩)
    have haltfalse (horders : Nat.card J = (Fintype.card F).factorial ∨
        Nat.card J = (Fintype.card F).factorial / 2) : False := by
      have hAlt := FiveTransitive.FixedActionGoursat.alternatingGroup_le_of_card_eq_factorial_or_half
        F J (by rw [← Nat.card_eq_fintype_card,hf24]; norm_num) horders
      have hb := (fixed_card_bound_of_alternating_normalizer_action X P s hs S hAlt).2
        (by norm_num : 3 ≠ 2)
      change Fintype.card F - 5 < 3 at hb
      rw [← Nat.card_eq_fintype_card,hf24] at hb
      omega
    rcases hclass with hsym | halt | hm
    · exact haltfalse (Or.inl (by rwa [Nat.card_eq_fintype_card]))
    · exact haltfalse (Or.inr (by simpa only [Nat.card_eq_fintype_card] using halt.2))
    · let sF : Set F := {x | (x : X) ∈ s}
      have hsF := SylowFixedActionPrimeFree.base_subset_fixedPoints X P s S
      let e : s ≃ sF :=
        { toFun := fun x => ⟨⟨x.val,hsF x.property⟩,x.property⟩
          invFun := fun x => ⟨x.val.val,x.property⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hsFcard : sF.ncard = 5 := by
        rw [← Nat.card_coe_set_eq,Nat.card_congr e.symm,Nat.card_coe_set_eq,hs]
      let K := fixingSubgroup J sF
      have hindex : K.index = (Fintype.card F).descFactorial 5 :=
        GlobalCoefficientReduction.index_fixingSubgroup_five_eq_descFactorial F J hJ5 sF hsFcard
      rw [← Nat.card_eq_fintype_card,hf24] at hindex
      norm_num [Nat.descFactorial] at hindex
      have hmul := K.index_mul_card
      have hJcard : Nat.card J = 244823040 := by simpa only [Nat.card_eq_fintype_card] using hm.2
      rw [hindex,hJcard] at hmul
      have hKcard : Nat.card K = 48 := by omega
      have hfree := SylowFixedActionPrimeFree.prime_not_dvd_fixedAction_stabilizer_card X P s S
      change ¬ 3 ∣ Nat.card K at hfree
      exact hfree (by rw [hKcard]; norm_num)
  have hAlt : alternatingGroup F ≤ J := by
    by_cases h30 : Nat.card F = 30
    · have hJ5 : IsMultiplyPretransitive J F 5 := by
        constructor
        intro a b
        obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
        exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,DFunLike.ext _ _ hg⟩
      exact TwoPrimeCycleClassification.alternatingGroup_le 13 4 (by norm_num) (by norm_num) (Or.inr rfl) J
        (by rw [← Nat.card_eq_fintype_card]; exact h30) hJ5
    by_cases h33 : Nat.card F = 33
    · have hJ5 : IsMultiplyPretransitive J F 5 := by
        constructor
        intro a b
        obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
        exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,DFunLike.ext _ _ hg⟩
      exact PrimePredFour.alternatingGroup_le_of_sub_four_prime F J
        (by rw [← Nat.card_eq_fintype_card,h33]; norm_num) hJ5
        (by rw [← Nat.card_eq_fintype_card,h33]; norm_num)
    by_cases h36 : Nat.card F = 36
    · have hJ5 : IsMultiplyPretransitive J F 5 := by
        constructor
        intro a b
        obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
        exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,DFunLike.ext _ _ hg⟩
      exact Degree36Classification.alternatingGroup_le J
        (by rw [← Nat.card_eq_fintype_card]; exact h36) hJ5
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
  left
  change Nat.card F = 6
  omega

end FiveTransitive.Degree72ThreeFixed

end CFSG

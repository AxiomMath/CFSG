module

public import CFSG.Permutation.FiveTransitive.Degree67ElevenFixed
public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeSevenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeFixed

public section

namespace CFSG

namespace FiveTransitive.Degree67ElevenImage

open MulAction SylowFixedActionCore

private theorem not_alternating_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1)
    [Fintype (sylowFixedPoints X P s S)] :
    ¬ alternatingGroup (sylowFixedPoints X P s S) ≤
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  intro hAlt
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let rho := toPermHom N F
  have hF := Degree67ElevenFixed.fixed_card_eq_twelve P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 12 at hF
  have hQ : IsPGroup 11 Q := S.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective
    (fixingSubgroup P s).subtype_injective
  have hfixeq : (F : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx q
      exact hx (⟨⟨q.val,Q.le_normalizer q.property⟩,q.property⟩ : sylowInNormalizer X P s S)
    · intro hx q
      exact hx (⟨q.val.val,q.property⟩ : Q)
  have hsevenImage : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by norm_num : Nat.Prime 7) (by norm_num)
      (by rw [← Nat.card_eq_fintype_card,hF]; omega)).trans
      (Subgroup.card_dvd_of_le hAlt)
  have hsevenN : 7 ∣ Nat.card N := hsevenImage.trans (Subgroup.card_range_dvd rho)
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 hsevenN
  exact Degree67LargePrimeSevenCentralizer.excluded P hcard h5 hnotAlt 11 (by norm_num)
    (Or.inl rfl) Q hQ
    (by rw [hQcard]; exact Degree67ElevenFixed.card_le_one_twenty_one P hcard h5 hnotAlt s hs S)
    (by rw [← hfixeq,hF]; omega) z hz

theorem fixed_card_image_and_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 12 ∧
      Nat.card (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = 95040 ∧
      Nat.card S ≤ 121 := by
  classical
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let J := (toPermHom N F).range
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype J := Fintype.ofFinite _
  have hF := Degree67ElevenFixed.fixed_card_eq_twelve P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 12 at hF
  have hN5 := (Degree67LargePrimeFixed.bounds_and_transitive 11 (by norm_num)
    P hcard h5 hnotAlt s hs S hS).2.2
  have hJ5 : ∀ a b : Fin 5 → F, Function.Injective a → Function.Injective b →
      ∃ g : J, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := hN5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,fun i => DFunLike.congr_fun hg i⟩
  have hclass := Helpers.classification_of_five_transitive_of_card_eq_twelve J F
    (by rwa [← Nat.card_eq_fintype_card]) hJ5
  have hnot := not_alternating_image P hcard h5 hnotAlt s hs S hS
  have horder : Nat.card J = 95040 := by
    rcases hclass with hsym | ⟨_,halt⟩ | ⟨_,hmathieu⟩
    · exact False.elim (hnot (FixedActionGoursat.alternatingGroup_le_of_card_eq_factorial_or_half
        F J (by rw [← Nat.card_eq_fintype_card,hF]; omega)
        (Or.inl (by simpa only [Nat.card_eq_fintype_card] using hsym))))
    · exact False.elim (hnot (FixedActionGoursat.alternatingGroup_le_of_card_eq_factorial_or_half
        F J (by rw [← Nat.card_eq_fintype_card,hF]; omega)
        (Or.inr (by simpa only [Nat.card_eq_fintype_card] using halt))))
    · simpa only [Nat.card_eq_fintype_card] using hmathieu
  exact ⟨hF,horder,Degree67ElevenFixed.card_le_one_twenty_one P hcard h5 hnotAlt s hs S⟩

end FiveTransitive.Degree67ElevenImage

end CFSG

module

public import CFSG.Permutation.FiveTransitive.Degree36NormalizerFixedDegree
public import CFSG.Permutation.FiveTransitive.SylowTwoFixedDegreeBounded

public section

namespace CFSG

namespace FiveTransitive.Degree36SylowTwoEntrance

open MulAction FixedNormalizerAction SylowFixedActionCore

private theorem one_hundred_twenty_eight_dvd_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    128 ∣ Nat.card S := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hd : 2^7 ∣ Nat.card (fixingSubgroup P s) := by
    rcases Degree36FourCases.card_cases P hcard h5 hnotAlt s hs with h | h | h | h <;>
      rw [h] <;> norm_num
  exact S.pow_dvd_card_of_pow_dvd_card hd

theorem fixed_six_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    IsPGroup 2 (sylowImage X P s S) ∧
    4 < Nat.card (sylowImage X P s S) ∧
    Nat.card (Fixed (X := X) (sylowImage X P s S)) = 6 ∧
      Image (X := X) (sylowImage X P s S) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hdiv := one_hundred_twenty_eight_dvd_card P hcard h5 hnotAlt s hs S
  have hlo : 128 ≤ Nat.card S := Nat.le_of_dvd (Nat.card_pos) hdiv
  have hlarge : 4 < Nat.card Q := by omega
  have hbase := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hbase
  have hb := SylowTwoFixedDegreeBounded.fixed_degree_le_eight_or_eq_twelve X P h5 s hs S
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % 2 = Nat.card F % 2 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  change 5 ≤ Nat.card F at hbase
  change Nat.card F ≤ 8 ∨ Nat.card F = 12 at hb
  have hcases : Nat.card (Fixed (X := X) Q) = 6 ∨
      Nat.card (Fixed (X := X) Q) = 8 ∨ Nat.card (Fixed (X := X) Q) = 12 := by
    change Nat.card F = 6 ∨ Nat.card F = 8 ∨ Nat.card F = 12
    omega
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hNexp := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hN5 : IsMultiplyPretransitive N F 5 :=
    FiveTransitive.isMultiplyPretransitive_of_explicit N F 5 hNexp
  exact ⟨hQ,hlarge,Degree36NormalizerFixedDegree.fixed_six_and_image P hcard h5 hnotAlt Q hN5 hcases⟩

end FiveTransitive.Degree36SylowTwoEntrance

end CFSG

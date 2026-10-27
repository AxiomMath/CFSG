module

public import CFSG.Permutation.FiveTransitive.Degree53SevenAutSectionOrbit
public import CFSG.Permutation.FiveTransitive.Degree53SevenAutSectionAlgebra
public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenGeneralData
public import CFSG.Permutation.FiveTransitive.SmallTwoGroupFiveElementary

public section

namespace CFSG

namespace FiveTransitive.Degree53SevenAutSection

open MulAction Subgroup FixedNormalizerAction

private theorem centralizer_prime_free
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (him : Image (X := X) Q = ⊤) :
    (¬ 5 ∣ Nat.card (centralizer (Q : Set P))) ∧
      (¬ 7 ∣ Nat.card (centralizer (Q : Set P))) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x,hx,_,_,hsmall⟩ := Degree53TwoSevenGeneralData.exists_orbit_data
    P hcard h5 hnotAlt Q hQ hF (by rw [him]; exact le_top)
  constructor
  · apply Degree53SevenAutSectionOrbit.centralizer_prime_free P Q x hx hsmall (by norm_num)
    intro g hg
    rw [Degree53FiveFree.fixed_card_eq_three P hcard h5 hnotAlt g hg]
    norm_num
  · apply Degree53SevenAutSectionOrbit.centralizer_prime_free P Q x hx hsmall (by norm_num)
    intro g hg
    rw [Degree53SevenFree.fixed_card_eq_four P hcard h5 hnotAlt g hg]
    norm_num

theorem exists_surjective_aut_image_hom
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (him : Image (X := X) Q = ⊤) :
    ∃ tau : Q.normalizerMonoidHom.range →* Equiv.Perm (Fixed (X := X) Q),
      Function.Surjective tau := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  have hseven := (centralizer_prime_free P hcard h5 hnotAlt Q hQ hF him).2
  have hkerCard : Nat.card Q.normalizerMonoidHom.ker = Nat.card (centralizer (Q : Set P)) := by
    rw [Q.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (centralizer_le_normalizer (Q : Set P))).toEquiv
  apply Degree53SevenAutSectionAlgebra.exists_surjective_range_hom hF Q.normalizerMonoidHom
    (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (MonoidHom.range_eq_top.mp him)
  rwa [hkerCard]

theorem elementary_of_card_sixteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (him : Image (X := X) Q = ⊤) (hQcard : Nat.card Q = 16) :
    IsMulCommutative Q ∧ ∀ q : Q, q ^ 2 = 1 := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  have hfive := (centralizer_prime_free P hcard h5 hnotAlt Q hQ hF him).1
  have hkerCard : Nat.card Q.normalizerMonoidHom.ker = Nat.card (centralizer (Q : Set P)) := by
    rw [Q.normalizerMonoidHom_ker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (centralizer_le_normalizer (Q : Set P))).toEquiv
  have hd : 5 ∣ Nat.card (MulAut Q) :=
    Degree53SevenAutSectionAlgebra.five_dvd_codomain hF Q.normalizerMonoidHom
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (MonoidHom.range_eq_top.mp him)
      (by rwa [hkerCard])
  exact (SmallTwoGroupFiveElementary.of_five_dvd_aut_card hQ hQcard.le hd).2

end FiveTransitive.Degree53SevenAutSection

end CFSG

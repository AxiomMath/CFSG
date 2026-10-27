module

public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenGeneralOdd

public section

namespace CFSG

namespace FiveTransitive.Degree53TwoSevenGeneralEven

open MulAction FixedNormalizerAction

theorem card_eq_sixteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (heven : P ≤ alternatingGroup X)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (him : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q) : Nat.card Q = 16 := by
  classical
  have hnot32 : Nat.card Q ≠ 32 := by
    intro he
    obtain ⟨z,hz⟩ := Degree53TwoSevenGeneralOdd.exists_odd_of_card_thirty_two
      P hcard h5 hnotAlt Q hQ hF him he
    exact hz (heven z.val.property)
  obtain ⟨x,_,himage,hker,_⟩ := Degree53TwoSevenGeneralData.exists_orbit_data
    P hcard h5 hnotAlt Q hQ hF him
  let f := toPermHom Q (orbit Q x)
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hm
  change Nat.card f.ker * Nat.card f.range = Nat.card Q at hm
  change Nat.card f.range = 16 at himage
  change Nat.card f.ker ≤ 2 at hker
  rw [himage] at hm
  have hp : 0 < Nat.card f.ker := Nat.card_pos
  omega

end FiveTransitive.Degree53TwoSevenGeneralEven

end CFSG

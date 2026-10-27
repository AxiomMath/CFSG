module

public import CFSG.Permutation.FiveTransitive.Degree48FiveFixerCard
public import CFSG.Permutation.FiveTransitive.Degree48ElevenFiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree48Classification
open MulAction

theorem alternatingGroup_le
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) : alternatingGroup X ≤ P := by
  classical
  by_contra hnotAlt
  let S : Sylow 11 P := Sylow.nonempty.some
  obtain ⟨d,hd,h24,hmod,hprod,hN⟩ :=
    Degree48LargeSylowActual.eleven_normalizer_constraints P hcard h5 hnotAlt S
  have hd5 := Degree48FiveFixerNumeric.eleven_five_dvd hd h24 hmod
    (hprod.trans (Degree48FiveFixerCard.ambient_card P hcard h5 hnotAlt))
  have hN5 : 5 ∣ Nat.card (Subgroup.normalizer (S : Set P)) := by
    rw [hN]
    exact hd5.mul_right 11
  exact Degree48ElevenFiveFree.normalizer_not_dvd P hcard h5 hnotAlt
    (Degree48FiveFixerCard.five_not_dvd P hcard h5 hnotAlt) S hN5

end FiveTransitive.Degree48Classification

end CFSG

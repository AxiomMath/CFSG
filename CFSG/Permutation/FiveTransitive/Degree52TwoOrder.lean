module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOrderData

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOrder

open MulAction SylowFixedActionCore

theorem card_sixteen_or_thirtyTwo
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card S = 16 ∨ Nat.card S = 32 := by
  let Q := sylowImage X P s S
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  obtain ⟨x,_,himage,hker,_⟩ :=
    Degree52TwoOrderData.exists_orbit_data P hcard h5 hnotAlt s hs S
  let f := toPermHom Q (orbit Q x)
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hm
  change Nat.card f.ker * Nat.card f.range = Nat.card Q at hm
  change Nat.card f.range = 16 at himage
  change Nat.card f.ker ≤ 2 at hker
  rw [himage,hQcard] at hm
  omega

end FiveTransitive.Degree52TwoOrder

end CFSG

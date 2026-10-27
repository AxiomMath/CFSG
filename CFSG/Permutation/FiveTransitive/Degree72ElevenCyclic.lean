module

public import CFSG.Permutation.FiveTransitive.ElevenCentralizingFive
public import CFSG.Permutation.FiveTransitive.Degree72ElevenSylow
public import CFSG.Permutation.FiveTransitive.Degree72ElevenCentralizingActual

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenCyclic
open MulAction SylowFixedActionCore

theorem card_eq_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 11 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : Nat.card S = 11 := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hQ : IsPGroup 11 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective
    (fixingSubgroup P s).subtype_injective
  have hn : Nat.card X < 11 ^ 2 := by rw [Nat.card_eq_fintype_card,hcard]; decide
  let _ : IsMulCommutative Q := Degree72LargePrimeOrbitImage.isMulCommutative 11 (by decide) hQ
    (Degree72LargePrimeOrbitSize.card_le_prime 11 (by decide) hQ hn)
  have hp (q : Q) : q ^ 11 = 1 := by
    obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp hQ q
    apply Subtype.ext
    apply Subtype.ext
    exact PrimePowerSmallDegree.pow_eq_one (by decide : Nat.Prime 11)
      (by rw [hcard]; decide) q.val.val ⟨e,by
        rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
        exact he⟩
  have hb : Nat.card Q ≤ 1331 := by
    rw [hQcard]
    exact Degree72ElevenSylow.card_le_cube P hcard h5 hnotAlt s hs S
  have hF : Nat.card F = 6 := Degree72ElevenFixed.fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  have him : (toPermHom N F).range = ⊤ := Degree72ElevenFixed.image_eq_top P hcard h5 hnotAlt s hs S hS
  obtain ⟨g,hg,hcomm⟩ := ElevenCentralizingFive.exists_five Q inferInstance hp hb hF (toPermHom N F) him
  rw [← hQcard]
  apply Degree72ElevenCentralizingActual.card_eq_eleven P hcard h5 hnotAlt Q _
    (Degree72LargePrimeOrbitSize.card_eq_prime 11 (by decide) hQ hn) g hg hcomm
  rw [← FixedNormalizerAction.fixed_eq Q]
  exact hF

end FiveTransitive.Degree72ElevenCyclic

end CFSG

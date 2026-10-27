module

public import CFSG.Permutation.FiveTransitive.Degree67ElevenImage
public import CFSG.Permutation.FiveTransitive.Degree67ElevenThreeObstruction
import CFSG.Permutation.FiveTransitive.Degree67FiveFree
public import CFSG.Permutation.FiveTransitive.ElevenNormalizerThreeCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree67ElevenFree
open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 11 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro hd
  let S : Sylow 11 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 11 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hdiv; norm_num at hdiv
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite _
  obtain ⟨hF,hJ,hbound⟩ := Degree67ElevenImage.fixed_card_image_and_bound P hcard h5 hnotAlt s hs S hS
  have hQ : IsPGroup 11 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q ≤ 121 := by
    rwa [Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective]
  have hN : 9 ∣ Nat.card N := by
    have h9 : 9 ∣ Nat.card (toPermHom N F).range := by rw [hJ]; norm_num
    exact h9.trans (Subgroup.card_range_dvd _)
  obtain ⟨g,hg,hcomm⟩ := ElevenNormalizerThreeCentralizer.exists_order_three Q hQ hQcard hN
  apply Degree67ElevenThreeObstruction.false_of_fixed_counts P hcard Q hQ _ g hg hcomm
    (FiveTransitive.Degree67FiveFree.three_fixed_card_le_four P hcard h5 hnotAlt g.val ((Subgroup.orderOf_coe g).trans hg))
  rw [← FixedNormalizerAction.fixed_eq Q]
  exact hF

end FiveTransitive.Degree67ElevenFree

end CFSG

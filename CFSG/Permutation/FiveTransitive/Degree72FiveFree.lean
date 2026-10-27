module

public import CFSG.Permutation.FiveTransitive.Degree72ElevenAmbientFree

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveFree
open MulAction SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hS5 : 5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hS5; norm_num at hS5
  have hF := Degree72FiveActual.fixed_card_eq_twelve P hcard h5 hnotAlt s hs S hS
  have hJ := Degree72FiveImage.card_eq_95040 P hcard h5 hnotAlt s hs S hF
  have hdJ : 11 ∣ Nat.card (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
    rw [hJ]; norm_num
  exact Degree72ElevenAmbientFree.not_dvd_ambient P hcard h5 hnotAlt
    ((hdJ.trans (Subgroup.card_range_dvd _)).trans (Subgroup.card_subgroup_dvd_card _))

end FiveTransitive.Degree72FiveFree

end CFSG

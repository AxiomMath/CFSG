module

public import CFSG.Permutation.FiveTransitive.Degree79SevenFixed

public section

namespace CFSG

namespace FiveTransitive.Degree79SevenFiveLift
open MulAction SylowFixedActionCore

theorem exists_normalizer_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 5 ∧
      Nat.card (Function.fixedPoints g.val.val) ≤ 39 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨hF,hAlt⟩ := Degree79SevenFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 9 at hF
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 5 ∣ Nat.card rho.range := by
    have ha : 5 ∣ Nat.card (alternatingGroup F) := by
      rw [nat_card_alternatingGroup,hF]
      norm_num [Nat.factorial]
    exact ha.trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hd.trans (Subgroup.card_range_dvd rho))
  have hgP : orderOf g.val = 5 := (Subgroup.orderOf_coe g).trans hg
  have hgperm : orderOf g.val.val = 5 := (Subgroup.orderOf_coe g.val).trans hgP
  have hne : g.val.val ≠ 1 := by intro he; rw [he,orderOf_one] at hgperm; omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
    hnotAlt g.val.property hne
  rw [hcard] at hb
  refine ⟨g,hg,?_⟩
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
  omega

end FiveTransitive.Degree79SevenFiveLift

end CFSG

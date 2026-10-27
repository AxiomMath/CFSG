module

public import CFSG.Permutation.FiveTransitive.Degree53SevenFixed
public import CFSG.Permutation.FiveTransitive.Degree53SevenBound
public import CFSG.Permutation.FiveTransitive.Degree53SevenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree53SevenElevenAut
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree53SevenOrder

open MulAction SylowFixedActionCore

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : False := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  obtain ⟨hF,hAlt⟩ := Degree53SevenFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 11 at hF
  change alternatingGroup F ≤ rho.range at hAlt
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hQfixed : Nat.card (fixedPoints Q X) = 11 := by rw [← hfixeq]; exact hF
  have hQbound := Degree53SevenBound.card_le_three_hundred_forty_three P hcard h5 hnotAlt Q hQ hQfixed
  have heleven : 11 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by norm_num : Nat.Prime 11) (by norm_num)
      (by rw [← Nat.card_eq_fintype_card,hF])).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 11
    (heleven.trans (Subgroup.card_range_dvd rho))
  have hz11 : z ^ 11 = 1 := hz ▸ pow_orderOf_eq_one z
  have haut : Q.normalizerMonoidHom z = 1 :=
    Degree53SevenElevenAut.eq_one Q hQ hQbound _
      (by rw [← map_pow,hz11,map_one])
  have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
    intro q
    have hh : z.val * q.val * z.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun a : P => a * z.val) hh
  have hQone := Degree53SevenCentralizer.card_eq_one P hcard h5 hnotAlt Q hQ z.val
    ((Subgroup.orderOf_coe z).trans hz) hcomm
  exact hS (hQcard.symm.trans hQone)

end FiveTransitive.Degree53SevenOrder

end CFSG

module

public import CFSG.Permutation.FiveTransitive.Degree48SevenFixed
public import CFSG.Permutation.FiveTransitive.Degree48SevenBound
public import CFSG.Permutation.FiveTransitive.Degree48SevenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree48SevenAut
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree48SevenOrder

open MulAction SylowFixedActionCore

private theorem card_eq_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : Nat.card S = 7 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  obtain ⟨hF,hImage⟩ := Degree48SevenFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 6 at hF
  change rho.range = ⊤ at hImage
  have hAlt : alternatingGroup F ≤ rho.range := hImage ▸ le_top
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hQfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← hfixeq]; exact hF
  have hQbound := Degree48SevenBound.card_le_three_hundred_forty_three P hcard h5 hnotAlt Q hQ hQfixed
  have hfive : 5 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by norm_num : Nat.Prime 5) (by norm_num)
      (by rw [← Nat.card_eq_fintype_card,hF]; norm_num)).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hfive.trans (Subgroup.card_range_dvd rho))
  have hz5 : z ^ 5 = 1 := hz ▸ pow_orderOf_eq_one z
  have haut : Q.normalizerMonoidHom z = 1 :=
    Degree48SevenAut.eq_one Q hQ hQbound _
      (by rw [← map_pow,hz5,map_one])
  have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
    intro q
    have hh : z.val * q.val * z.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun a : P => a * z.val) hh
  have hQseven := Degree48SevenCentralizer.card_le_seven P hcard h5 hnotAlt Q hQ z.val
    ((Subgroup.orderOf_coe z).trans hz) hcomm
  rw [hQcard] at hQseven
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 7) (by omega : 2 ≤ e)
    rw [← he] at hh
    change 49 ≤ Nat.card S at hh
    omega
  have he0 : e ≠ 0 := by intro h; apply hS; rw [he,h,pow_zero]
  have heq : e = 1 := by omega
  rw [he,heq,pow_one]

theorem forty_nine_not_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 49 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 (fixingSubgroup P s) := default
  intro hd
  have h49 : 49 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 2) hd
  by_cases hS : Nat.card S = 1
  · rw [hS] at h49
    norm_num at h49
  · rw [card_eq_seven P hcard h5 hnotAlt s hs S hS] at h49
    norm_num at h49

end FiveTransitive.Degree48SevenOrder

end CFSG

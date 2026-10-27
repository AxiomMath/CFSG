module

public import CFSG.Permutation.FiveTransitive.Degree54FiveSylowData
public import CFSG.Permutation.FiveTransitive.Degree54FiveSevenCentralizer
public import CFSG.Permutation.FiveTransitive.FiveGroupSmallSevenAutomorphism

public section

namespace CFSG

namespace FiveTransitive.Degree54SylowFiveOrder

open MulAction Subgroup SylowFixedActionCore

theorem sylow_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : Nat.card S = 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  obtain ⟨hF,hAlt⟩ := Degree54FiveSylowData.five_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 9 at hF
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 9 := by rwa [← hfixeq]
  have hQcard := Degree54FiveGroupBound.card_le_six_hundred_twenty_five P hcard h5 hnotAlt Q hQ hfixed.ge
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hd : 7 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; omega)).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hd.trans (Subgroup.card_range_dvd rho))
  have haut : Q.normalizerMonoidHom g = 1 :=
    FiveGroupSmallSevenAutomorphism.eq_one hQ hQcard _
      (by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun a : P => a * g.val) hh
  have hle := Degree54FiveSevenCentralizer.card_le_five P hcard h5 hnotAlt Q hQ
    g.val ((Subgroup.orderOf_coe g).trans hg) hcomm
  have heq : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  rw [heq] at hle
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hepos : 1 ≤ e := by
    by_contra hn
    exact hS (by rw [he,show e=0 by omega,pow_zero])
  have hge : 5 ≤ Nat.card S := by rw [he]; exact Nat.pow_le_pow_right (by decide : 0 < 5) hepos
  omega

end FiveTransitive.Degree54SylowFiveOrder

end CFSG

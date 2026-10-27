module

public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeSevenLift
public import CFSG.Permutation.FiveTransitive.Degree69NineteenAut
public import CFSG.Permutation.FiveTransitive.Degree69NineteenCentralizer
import CFSG.Permutation.FiveTransitive.Degree69FiveTupleDivisibility

public section

namespace CFSG

namespace FiveTransitive.Degree69NineteenFree
open MulAction Subgroup SylowFixedActionCore

private theorem fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 19 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) = 12 := by
  by_contra hn
  have h7 := Degree69LargePrimeSevenLift.seven_dvd_normalizer 19 (by norm_num)
    (by omega) P hcard h5 hnotAlt s hs S hS hn
  exact hseven (h7.trans (Subgroup.card_subgroup_dvd_card (sylowNormalizer X P s S)))

private theorem image_card_le_square
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 19 Q)
    (hF : Nat.card (fixedPoints Q X) = 12) : Nat.card Q ≤ 19 ^ 2 := by
  let _ : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hd := FiveTransitive.Degree69FiveTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q 23 (by omega)
  rw [hF] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he2 : e ≤ 2 := by
    by_contra hn
    have hh : 19 ^ 3 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 19 (by omega : 3 ≤ e)
    have hh := hh.trans hd
    norm_num [Nat.descFactorial] at hh
  rw [he]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 19) he2

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (s : Set X) (hs : s.ncard = 5) :
    ¬ 19 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  intro hd
  let S : Sylow 19 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 19 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hdiv; norm_num at hdiv
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite _
  have hQ : IsPGroup 19 Q := S.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective
  have hF : Nat.card F = 12 := fixed_card P hcard h5 hnotAlt hseven s hs S hS
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hbound := image_card_le_square P hcard h5 hnotAlt Q hQ (by rw [← hfixeq]; exact hF)
  obtain ⟨hlo,_,hN5⟩ := Degree69LargePrimeFixed.bounds_and_transitive 19 (by norm_num)
    P hcard h5 hnotAlt s hs S hS
  have hdN := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
    (by rw [← Nat.card_eq_fintype_card,hF]; omega) hN5
  rw [← Nat.card_eq_fintype_card,hF] at hdN
  have h11 : 11 ∣ Nat.card N := (by norm_num [Nat.descFactorial] : 11 ∣ (12 : ℕ).descFactorial 5).trans hdN
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 11 h11
  have hcent := Degree69NineteenAut.centralizes Q hQ hbound z (hz ▸ pow_orderOf_eq_one z)
  have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
    intro q
    exact (hcent q.val q.property).symm
  have hone := Degree69NineteenCentralizer.card_eq_one P hcard h5 hnotAlt Q hQ z.val
    ((Subgroup.orderOf_coe z).trans hz) hcomm
  exact hS (hQcard ▸ hone)

end FiveTransitive.Degree69NineteenFree

end CFSG

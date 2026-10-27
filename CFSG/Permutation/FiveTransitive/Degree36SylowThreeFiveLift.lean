module

public import CFSG.Permutation.FiveTransitive.Degree36FivePower
import CFSG.Permutation.FiveTransitive.Degree28SmallTwoFiveFixed
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG

namespace FiveTransitive.Degree36SylowThreeFiveLift

open MulAction SylowFixedActionCore

theorem exists_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ z : sylowNormalizer X P s S, orderOf z = 5 ∧
      orderOf (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S) z) = 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  obtain ⟨hF,hImage⟩ := Degree36SmallPrimeEntrance.three_fixed_card_and_image
    P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 6 at hF
  change rho.range = ⊤ at hImage
  have hAlt : alternatingGroup F ≤ rho.range := by rw [hImage]; exact le_top
  have hdiv : 5 ∣ Nat.card rho.range :=
    (odd_prime_dvd_alternating_card F (by norm_num : Nat.Prime 5) (by norm_num)
      (by rw [← Nat.card_eq_fintype_card,hF]; norm_num)).trans (Subgroup.card_dvd_of_le hAlt)
  let T : Sylow 5 N := Sylow.nonempty.some
  have hex : ∃ z : N, z ∈ (T : Subgroup N) ∧ rho z ≠ 1 := by
    by_contra hn
    push Not at hn
    exact prime_not_dvd_range_card_of_sylow_le_ker T rho (fun z hz => hn z hz) hdiv
  obtain ⟨z,hzT,hzrho⟩ := hex
  obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' (⟨z,hzT⟩ : T)
  have hzorder : orderOf z = 5 ^ e := (Subgroup.orderOf_coe (⟨z,hzT⟩ : T)).trans he
  have hzpow : z ^ 5 = 1 := by
    apply Subtype.ext
    exact Degree36FivePower.pow_five_eq_one P hcard h5 hnotAlt z.val
      ⟨e,(Subgroup.orderOf_coe z).trans hzorder⟩
  refine ⟨z,orderOf_eq_prime hzpow ?_,orderOf_eq_prime ?_ hzrho⟩
  · intro hz
    exact hzrho (by rw [hz,map_one])
  · rw [← map_pow,hzpow,map_one]

theorem exists_five_fixed_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ z : sylowNormalizer X P s S, orderOf z = 5 ∧
      orderOf (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S) z) = 5 ∧
      Nat.card (Function.fixedPoints
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S) z)) = 1 := by
  classical
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  obtain ⟨z,hz,hlocal⟩ := exists_five P hcard h5 hnotAlt s hs S hS
  have hF := (Degree36SmallPrimeEntrance.three_fixed_card_and_image
    P hcard h5 hnotAlt s hs S hS).1
  change Nat.card F = 6 at hF
  exact ⟨z,hz,hlocal,FiveTransitive.Degree28SmallTwoFiveFixed.local_fixed_eq_one (by rwa [← Nat.card_eq_fintype_card]) _ hlocal⟩

end FiveTransitive.Degree36SylowThreeFiveLift

end CFSG

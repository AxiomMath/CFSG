module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import CFSG.GroupTheory.PermSylowTwo.Alt
import CFSG.GroupTheory.AlternatingFive.SylowTwo
import CFSG.GroupTheory.SolvableHallNodes
import CFSG.GroupTheory.WielandtProductFinal
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
public import CFSG.Assembly.QuasithinDefs
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open scoped Pointwise

private theorem le_of_isSylowTwoOf_of_not_three_dvd_alt_five {X : Type} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 5)) {S H : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hSH : S ≤ H) (h3 : ¬ 3 ∣ Nat.card ↥H) :
    H ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : Nat.card X = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  obtain ⟨-, hS2, hSidx⟩ := hS
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hidx : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [hidx] at hSidx
  have hmul := Subgroup.card_mul_index S
  rw [hk, hX] at hmul
  have hk2 : 2 ^ k = 4 := by
    have hk6 : k < 6 := by
      by_contra hc
      have h64 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hpos : 0 < S.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      nlinarith
    interval_cases k <;> omega
  have hH60 : Nat.card ↥H ∣ 60 := hX ▸ Subgroup.card_subgroup_dvd_card H
  have h4 : 4 ∣ Nat.card ↥H := by
    have := Subgroup.card_dvd_of_le hSH
    rwa [hk, hk2] at this
  have h20 : Nat.card ↥H ≠ 20 := by
    have := CFSG.GroupTheory.AlternatingFive.card_ne_twenty (H.map e.toMonoidHom)
    rwa [Subgroup.card_map_of_injective e.injective] at this
  have hmem : Nat.card ↥H ∈ Nat.divisors 60 := Nat.mem_divisors.mpr ⟨hH60, by norm_num⟩
  have hdiv : Nat.divisors 60 = {1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60} := by decide
  rw [hdiv] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hH4 : Nat.card ↥H = 4 := by
    rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h <;> omega
  exact (Subgroup.eq_of_le_of_card_ge hSH (by rw [hH4, hk, hk2])).ge

theorem le_of_isSylowTwoOf_of_not_three_dvd_alt {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 5 ≤ m) (e : X ≃* alternatingGroup (Fin m)) {S H : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hSH : S ≤ H) (h3 : ¬ 3 ∣ Nat.card ↥H) :
    H ≤ S := by
  rcases Nat.lt_or_ge m 6 with h6 | h6
  · obtain rfl : m = 5 := by omega
    exact le_of_isSylowTwoOf_of_not_three_dvd_alt_five e hS hSH h3
  · exact CFSG.GroupTheory.PermSylowTwo.le_of_isSylowTwoOf_of_mulEquiv_alt h6
      (Subgroup.topEquiv.trans e) hS hSH le_top h3

theorem isPGroup_three_of_permutes_alt {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 5 ≤ m)
    (e : X ≃* alternatingGroup (Fin m)) {S B : Subgroup X}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hBn : Group.IsNilpotent ↥B)
    (hBo : Odd (Nat.card ↥B)) (hBS : (B : Set X) * (S : Set X) = (S : Set X) * (B : Set X)) :
    IsPGroup 3 ↥B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS2 : IsPGroup 2 ↥S := hS.2.1
  have hcoe : ((B ⊔ S : Subgroup X) : Set X) = (B : Set X) * (S : Set X) :=
    CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hBS
  have hBY : B ≤ B ⊔ S := le_sup_left
  have hSY : S ≤ B ⊔ S := le_sup_right
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hsolv : Group.IsSolvable ↥(B ⊔ S) := by
    have eB : ↥(B.subgroupOf (B ⊔ S)) ≃* ↥B := Subgroup.subgroupOfEquivOfLe hBY
    have eS : ↥(S.subgroupOf (B ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSY
    haveI := hBn
    refine CFSG.GroupTheory.WielandtProduct.wielandt_coprime_product (B.subgroupOf (B ⊔ S))
      (S.subgroupOf (B ⊔ S)) (Group.nilpotent_of_mulEquiv eB.symm)
      ((hS2.of_equiv eS.symm).isNilpotent) ?_ ?_
    · rw [Nat.card_congr eB.toEquiv, Nat.card_congr eS.toEquiv, hk]
      exact (Nat.coprime_two_right.2 hBo).pow_right k
    · intro g
      have hg : (g : X) ∈ ((B ⊔ S : Subgroup X) : Set X) := g.2
      rw [hcoe] at hg
      obtain ⟨b, hb, s, hs, hbs⟩ := hg
      exact ⟨⟨b, hBY hb⟩, hb, ⟨s, hSY hs⟩, hs, Subtype.ext hbs.symm⟩
  let π : Set Nat.Primes := {p | p.val ≠ 3}
  have hU : CFSG.IsPiSubgroup π (S.subgroupOf (B ⊔ S)) := by
    intro p hp
    have hp' : p.val ∣ 2 ^ k := by
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv, hk] at hp
    have h2 : p.val = 2 :=
      (Nat.prime_dvd_prime_iff_eq p.prop Nat.prime_two).1 (p.prop.dvd_of_dvd_pow hp')
    show p.val ≠ 3
    omega
  obtain ⟨H, hH, hSH⟩ := CFSG.SolvableHall.solvable_hall_containment hsolv π _ hU
  have hcardH : Nat.card ↥(H.map (B ⊔ S).subtype) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (B ⊔ S).subtype_injective
  have hSH' : S ≤ H.map (B ⊔ S).subtype := fun s hs =>
    ⟨⟨s, hSY hs⟩, hSH (show (⟨s, hSY hs⟩ : ↥(B ⊔ S)) ∈ S.subgroupOf (B ⊔ S) from hs), rfl⟩
  have h3H : ¬ 3 ∣ Nat.card ↥(H.map (B ⊔ S).subtype) := by
    rw [hcardH]
    intro h3
    exact hH.p_in_pi_of_p_dvd_card ⟨3, Nat.prime_three⟩ h3 rfl
  have hHS : H.map (B ⊔ S).subtype ≤ S := le_of_isSylowTwoOf_of_not_three_dvd_alt hm e hS hSH' h3H
  obtain ⟨j, hj⟩ := (hS2.to_le hHS).exists_card_eq
  rw [hcardH] at hj
  have hmul := Subgroup.card_mul_index H
  have hprime : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card ↥B → q = 3 := by
    intro q hq hqB
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hBo) (even_iff_two_dvd.2 hqB)
    have hqY : q ∣ Nat.card ↥H * H.index := hmul ▸ hqB.trans (Subgroup.card_dvd_of_le hBY)
    rw [hj] at hqY
    have hcop : Nat.Coprime q (2 ^ j) :=
      ((Nat.Prime.coprime_iff_not_dvd hq).2
        ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).not.2 hq2)).pow_right j
    have hqi : q ∣ H.index := hcop.dvd_of_dvd_mul_left hqY
    by_contra hq3
    exact hH.p_in_pi_of_p_dvd_index ⟨q, hq⟩ hqi hq3
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.GroupTheory.WielandtProductFinal
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open scoped Pointwise

@[expose] def K105Spor : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName), s ≠ .J1 → IsSpor X s →
    ∀ S H : Subgroup X, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ → S ≤ H → Group.IsSolvable ↥H →
      ¬ 3 ∣ Nat.card ↥H → H ≤ S

theorem isPGroup_three_of_permutes_spor (hK : K105Spor) {X : Type} [Group X] [Finite X]
    {s : TauCeti.SporadicName} (hs : s ≠ .J1) (hX : IsSpor X s) {S B : Subgroup X}
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
  have hHs : Group.IsSolvable ↥(H.map (B ⊔ S).subtype) := by
    have : Group.IsSolvable ↥H := Group.isSolvable_of_isSolvable_injective H.subtype_injective
    exact Group.isSolvable_of_surjective ((B ⊔ S).subtype.subgroupMap_surjective H)
  have hHS : H.map (B ⊔ S).subtype ≤ S := hK X s hs hX S _ hS hSH' hHs h3H
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

module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.TwoGroupQuadCommutatorCard

private theorem commutative_of_card_le_four
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hcard : Nat.card G ≤ 4) : IsMulCommutative G := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨e,he⟩ := hG.exists_card_eq
  have he2 : e ≤ 2 := by
    by_contra hn
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ e)
    rw [← he] at hpow
    norm_num at hpow
    omega
  interval_cases e
  · have hsmall : Subsingleton G := Finite.card_le_one_iff_subsingleton.mp (by simpa using he.le)
    let _ := hsmall
    rw [isMulCommutative_iff]
    exact fun a b => Subsingleton.elim _ _
  · have hcyc : IsCyclic G := isCyclic_of_prime_card (by simpa using he)
    let _ := hcyc
    exact IsCyclic.isMulCommutative
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq he

private theorem exists_central_card_two
    {G : Type*} [Group G] [Finite G] [Nontrivial G] (hG : IsPGroup 2 G) :
    ∃ C : Subgroup G, C ≤ Subgroup.center G ∧ Nat.card C = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Nontrivial (Subgroup.center G) := hG.center_nontrivial
  have hd : 2 ∣ Nat.card (Subgroup.center G) := by
    rcases (hG.to_subgroup (Subgroup.center G)).card_eq_or_dvd with h | h
    · have hh := Finite.one_lt_card (α := Subgroup.center G)
      omega
    · exact h
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 2 hd
  refine ⟨Subgroup.zpowers z.val,Subgroup.zpowers_le.mpr z.property,?_⟩
  rw [Nat.card_zpowers,Subgroup.orderOf_coe,hz]

theorem commutator_card_le_two
    {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (hcard : Nat.card G ≤ 8) : Nat.card (commutator G) ≤ 2 := by
  classical
  by_cases htriv : Subsingleton G
  · let _ := htriv
    have hh : Nat.card (commutator G) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
    omega
  · let _ : Nontrivial G := not_subsingleton_iff_nontrivial.mp htriv
    obtain ⟨C,hC,hCcard⟩ := exists_central_card_two hG
    let _ : C.Normal := Subgroup.normal_of_le_center hC
    have hquot : Nat.card (G ⧸ C) ≤ 4 := by
      have hh := C.card_eq_card_quotient_mul_card_subgroup
      rw [hCcard] at hh
      omega
    have hc := commutative_of_card_le_four (hG.to_quotient C) hquot
    have hle : commutator G ≤ C := Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hc
    exact (Subgroup.card_le_of_le hle).trans hCcard.le

end FiveTransitive.TwoGroupQuadCommutatorCard

end CFSG

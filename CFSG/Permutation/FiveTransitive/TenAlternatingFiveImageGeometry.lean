module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Data.Rat.Floor

public section

namespace CFSG

namespace FiveTransitive.TenAlternatingFiveImageGeometry

private theorem cycleType_eq_single_five
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Nat.card F = 10)
    (u : Equiv.Perm F) (hu : u ^ 5 = 1)
    (hfix : Nat.card (Function.fixedPoints u) = 5) : u.cycleType = {5} := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hu
  have hc := u.card_fixedPoints
  rw [← Nat.card_eq_fintype_card, hfix, ← Nat.card_eq_fintype_card, hF,
    ht, Multiset.sum_replicate, nsmul_eq_mul] at hc
  have hb := u.sum_cycleType_le
  rw [ht, Multiset.sum_replicate, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hF] at hb
  simp only [Nat.cast_id] at hc hb
  have hm : u.cycleType.card = 1 := by omega
  rw [ht, hm]
  rfl

theorem exists_commuting_three
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Nat.card F = 10)
    (u : Equiv.Perm F) (hu : u ^ 5 = 1)
    (hfix : Nat.card (Function.fixedPoints u) = 5) :
    ∃ v : alternatingGroup F, orderOf v = 3 ∧ Commute u v.val := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let C := Subgroup.centralizer ({u} : Set (Equiv.Perm F))
  have hC : Nat.card C = 600 := by
    rw [Equiv.Perm.nat_card_centralizer, cycleType_eq_single_five hF u hu hfix,
      ← Nat.card_eq_fintype_card, hF]
    norm_num [Nat.factorial]
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 (by rw [hC]; norm_num)
  have hv5 : v.val ^ 3 = 1 := by
    exact congrArg Subtype.val (hv ▸ pow_orderOf_eq_one v)
  have hsign : v.val.sign = 1 := by
    have hs := congrArg Equiv.Perm.sign hv5
    rw [map_pow, map_one] at hs
    rcases Int.units_eq_one_or v.val.sign with h | h
    · exact h
    · rw [h] at hs
      exact False.elim ((by decide : (-1 : ℤˣ) ^ 3 ≠ 1) hs)
  let w : alternatingGroup F := ⟨v.val, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  refine ⟨w, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe w]
    exact (Subgroup.orderOf_coe v).trans hv
  · exact (Subgroup.mem_centralizer_singleton_iff.mp v.property).symm

theorem fixed_five_of_centralizer_three_dvd
    {E : Type*} [Fintype E] [DecidableEq E] (hE : Nat.card E = 10)
    (p : Equiv.Perm E) (hp : p ^ 5 = 1) (hne : p ≠ 1)
    (hthree : 3 ∣ Nat.card (Subgroup.centralizer ({p} : Set (Equiv.Perm E)))) :
    Nat.card (Function.fixedPoints p) = 5 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have ht := Equiv.Perm.cycleType_of_pow_prime_eq_one hp
  have hb := p.sum_cycleType_le
  rw [ht, Multiset.sum_replicate, nsmul_eq_mul, ← Nat.card_eq_fintype_card, hE] at hb
  have hsum := p.sum_cycleType
  rw [ht, Multiset.sum_replicate, nsmul_eq_mul] at hsum
  have hpos : 0 < p.support.card := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hne (Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp hz))
  have hcases : p.cycleType.card = 1 ∨ p.cycleType.card = 2 := by
    simp only [Nat.cast_id] at hb hsum
    omega
  rcases hcases with hone | htwo
  · rw [Nat.card_eq_fintype_card, p.card_fixedPoints, ht, hone,
      ← Nat.card_eq_fintype_card, hE]
    norm_num
  · exfalso
    have hC : Nat.card (Subgroup.centralizer ({p} : Set (Equiv.Perm E))) = 50 := by
      rw [Equiv.Perm.nat_card_centralizer, ht, htwo, ← Nat.card_eq_fintype_card, hE]
      norm_num [Nat.factorial]
    rw [hC] at hthree
    norm_num at hthree

theorem exists_single_five
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Nat.card F = 10) :
    ∃ u : alternatingGroup F, orderOf u = 5 ∧
      Nat.card (Function.fixedPoints u.val) = 5 := by
  obtain ⟨p,hp⟩ := (Equiv.Perm.exists_with_cycleType_iff F).mpr
    (show ({5} : Multiset ℕ).sum ≤ Fintype.card F ∧
        ∀ a ∈ ({5} : Multiset ℕ), 2 ≤ a by
      rw [← Nat.card_eq_fintype_card,hF]
      norm_num)
  have heven : p.sign = 1 := by rw [Equiv.Perm.sign_of_cycleType,hp]; norm_num; decide
  let u : alternatingGroup F := ⟨p,Equiv.Perm.mem_alternatingGroup.mpr heven⟩
  refine ⟨u,?_,?_⟩
  · rw [← Subgroup.orderOf_coe u]
    change orderOf p = 5
    rw [← p.lcm_cycleType,hp]
    simp
  · change Nat.card (Function.fixedPoints p) = 5
    rw [Nat.card_eq_fintype_card,p.card_fixedPoints,hp,← Nat.card_eq_fintype_card,hF]
    norm_num

end FiveTransitive.TenAlternatingFiveImageGeometry

end CFSG

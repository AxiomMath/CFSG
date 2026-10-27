module

public import CFSG.Permutation.FiveTransitive.FreeComplementOrbitCount
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.FreeTwoGroupOddCyclic

open Equiv MulAction

theorem cycle_type
    {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [MulAction G X]
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1) (g : G) :
    (toPerm g : Perm X).cycleType =
      Multiset.replicate (toPerm g : Perm X).cycleType.card (orderOf g) := by
  apply Multiset.eq_replicate_of_mem
  intro n hn
  have hd : n ∣ orderOf g := (Perm.dvd_of_mem_cycleType hn).trans
    (orderOf_map_dvd (toPermHom G X) g)
  obtain ⟨c, t, hct, hdis, hc, hcard⟩ := Perm.mem_cycleType_iff.mp hn
  have hcn : c ^ n = 1 := by rw [← hcard, ← hc.orderOf]; exact pow_orderOf_eq_one c
  obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
    by_contra! h
    exact hc.ne_one (Perm.ext h)
  have htx : t x = x := (hdis x).resolve_left hx
  have hgfix : (g ^ n) • x = x := by
    change (toPerm (g ^ n) : Perm X) x = x
    rw [show toPerm (g ^ n) = (toPerm g : Perm X) ^ n from (toPermHom G X).map_pow g n,
      hct, hdis.commute.mul_pow, hcn, one_mul]
    exact Perm.pow_apply_eq_self_of_apply_eq_self htx n
  exact Nat.dvd_antisymm hd (orderOf_dvd_of_pow_eq_one (hfree _ x hgfix))

private theorem order_eq_card
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (hG : IsPGroup 2 G)
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (g : G) (hsign : Perm.sign (toPerm g : Perm X) = -1) :
    orderOf g = Nat.card G := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : Perm X := toPerm g
  have hg : g ≠ 1 := by
    intro he
    rw [he, toPerm_one, map_one] at hsign
    norm_num at hsign
  have hs : σ.support = Finset.univ := by
    ext x
    simp only [Perm.mem_support, Finset.mem_univ, iff_true]
    exact fun h => hg (hfree g x h)
  have hct := cycle_type hfree g
  have hcard : σ.cycleType.card * orderOf g = Nat.card X := by
    have hh := σ.sum_cycleType
    rw [hct, Multiset.sum_replicate, nsmul_eq_mul, hs, Finset.card_univ] at hh
    simpa only [Nat.cast_id, Nat.card_eq_fintype_card] using hh
  have horderEven : Even (orderOf g) := even_iff_two_dvd.mpr (hG.dvd_orderOf hg)
  have hsign' : (-1 : ℤˣ) ^ σ.cycleType.card = -1 := by
    rw [Perm.sign_of_cycleType, hct, Multiset.sum_replicate,
      Multiset.card_replicate, nsmul_eq_mul] at hsign
    simp only [Nat.cast_id] at hsign
    have he : Even (σ.cycleType.card * orderOf g) := horderEven.mul_left _
    rw [pow_add, he.neg_one_pow, one_mul] at hsign
    exact hsign
  have hkodd : ¬ 2 ∣ σ.cycleType.card := by
    intro hk
    have he : Even σ.cycleType.card := even_iff_two_dvd.mpr hk
    rw [he.neg_one_pow] at hsign'
    norm_num at hsign'
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hG
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hG g
  have hkm : k ≤ m := by
    apply (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp
    rw [← hm, ← hk]
    exact orderOf_dvd_natCard g
  have hmle : m ≤ k := by
    by_contra hh
    have hlt : k + 1 ≤ m := by omega
    have hd : orderOf g * 2 ∣ Nat.card G := by
      rw [hk, hm, ← pow_succ]
      exact Nat.pow_dvd_pow 2 hlt
    have hGdegree : Nat.card G ∣ Nat.card X := by
      rw [FreeComplementOrbitCount.card_eq_mul_orbits hfree]
      exact dvd_mul_right _ _
    have hdiv : orderOf g * 2 ∣ orderOf g * σ.cycleType.card := by
      rw [Nat.mul_comm (orderOf g) σ.cycleType.card, hcard]
      exact hd.trans hGdegree
    exact hkodd ((Nat.mul_dvd_mul_iff_left (by rw [hk]; positivity)).mp hdiv)
  rw [hk, hm, Nat.le_antisymm hkm hmle]

theorem generates
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (hG : IsPGroup 2 G)
    (hfree : ∀ (g : G) (x : X), g • x = x → g = 1)
    (g : G) (hsign : Perm.sign (toPerm g : Perm X) = -1) :
    Subgroup.zpowers g = ⊤ ∧ IsCyclic G := by
  have ho := order_eq_card hG hfree g hsign
  exact ⟨(Subgroup.zpowers g).eq_top_of_card_eq ((Nat.card_zpowers g).trans ho),
    isCyclic_of_orderOf_eq_card g ho⟩

end FiveTransitive.FreeTwoGroupOddCyclic

end CFSG

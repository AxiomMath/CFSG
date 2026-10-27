module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG

namespace FiveTransitive.FiveSevenFixedFree

open MulAction

private theorem fixed_card_eq_zero
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 5 Q)
    (hY : Fintype.card Y = 35) (hno : fixedPoints Q Y = ∅)
    (g : Equiv.Perm Y) (hg : g ^ 7 = 1) (hne : g ≠ 1)
    (hc : g ∈ Subgroup.centralizer (Q : Set (Equiv.Perm Y))) :
    Nat.card (Function.fixedPoints g) = 0 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let C : SubMulAction Q Y :=
    { carrier := Function.fixedPoints g
      smul_mem' := by
        intro q x hx
        change g (q.val x) = q.val x
        have hcomm : g * q.val = q.val * g :=
          ((Subgroup.mem_centralizer_iff.mp hc) q.val q.property).symm
        have hh := congrArg (fun a : Equiv.Perm Y => a x) hcomm
        change g (q.val x) = q.val (g x) at hh
        exact hh.trans (congrArg q.val hx) }
  have hempty : IsEmpty (fixedPoints Q C) := by
    refine ⟨fun x => ?_⟩
    have hx : x.val.val ∈ fixedPoints Q Y := by
      intro q
      exact congrArg Subtype.val (x.property q)
    rw [hno] at hx
    exact hx
  let _ := hempty
  have hmod5 := hQ.card_modEq_card_fixedPoints C
  change Nat.card C % 5 = Nat.card (fixedPoints Q C) % 5 at hmod5
  rw [Nat.card_of_isEmpty (α := fixedPoints Q C)] at hmod5
  change Nat.card (Function.fixedPoints g) % 5 = 0 at hmod5
  let f : Function.End Y := g.toFun
  have hf : f ^ 7 = 1 := by
    funext x
    change (g ^ 7) x = x
    rw [hg]
    rfl
  have hmod7 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 7) (n := 1)
    (by simpa only [pow_one] using hf)
  change Fintype.card Y % 7 = Fintype.card (Function.fixedPoints g) % 7 at hmod7
  rw [hY,← Nat.card_eq_fintype_card] at hmod7
  have hle : Nat.card (Function.fixedPoints g) ≤ 35 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.sum_cycleType,hY]
    omega
  have hcases : Nat.card (Function.fixedPoints g) = 0 ∨
      Nat.card (Function.fixedPoints g) = 35 := by omega
  rcases hcases with h | h
  · exact h
  · exfalso
    apply hne
    have hs : g.support.card = 0 := by
      rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.sum_cycleType,hY] at h
      have hb := Finset.card_le_univ g.support
      rw [hY] at hb
      omega
    exact Equiv.Perm.support_eq_empty_iff.mp (Finset.card_eq_zero.mp hs)

theorem centralizer_card
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 5 Q)
    (hY : Fintype.card Y = 35) (hno : fixedPoints Q Y = ∅)
    (g : Equiv.Perm Y) (hg : g ^ 7 = 1) (hne : g ≠ 1)
    (hc : g ∈ Subgroup.centralizer (Q : Set (Equiv.Perm Y))) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm Y))) = 120 * 7 ^ 5 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have ho : orderOf g = 7 := orderOf_eq_prime hg hne
  have hf := fixed_card_eq_zero Q hQ hY hno g hg hne hc
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (show (orderOf g).Prime by rw [ho]; decide)
  have hsum := g.sum_cycleType
  rw [hk,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,ho] at hsum
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.sum_cycleType,hY] at hf
  have hb := Finset.card_le_univ g.support
  rw [hY] at hb
  have he : k + 1 = 5 := by omega
  rw [Equiv.Perm.nat_card_centralizer,hk,ho,he,hY]
  norm_num [Nat.factorial]

end FiveTransitive.FiveSevenFixedFree

end CFSG

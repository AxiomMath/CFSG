module

public import CFSG.Permutation.FiveTransitive.Degree72FiveActual

public section

namespace CFSG

namespace FiveTransitive.Degree72ThreeFivePower
open MulAction Subgroup

private theorem twentyFive_dvd_complement
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (g : G) (hg : orderOf g = 25) :
    25 ∣ Nat.card X - (fixedBy X (g ^ 5)).ncard := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := zpowers g
  let a : A := ⟨g,mem_zpowers g⟩
  have ha : orderOf a = 25 := (Subgroup.orderOf_coe a).symm.trans hg
  have hAcard : Nat.card A = 25 := by rw [Nat.card_zpowers,hg]
  have hA : IsPGroup 5 A := IsPGroup.of_card (n := 2) hAcard
  let _ : IsMulCommutative A := IsCyclic.isMulCommutative
  have hd := FreeComplementCard.card_dvd_complement A X (fixedBy X (a ^ 5))
    (by
      intro q x hx
      change (a ^ 5) • (q • x) = q • x
      rw [← mul_smul,mul_comm' (a ^ 5) q,mul_smul,hx]) (by
      intro q x hx hqx
      by_contra hq
      obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp hA q
      have hepos : 1 ≤ e := by
        by_contra hn
        have he0 : e = 0 := by omega
        rw [he0,pow_zero] at he
        exact hq (orderOf_eq_one_iff.mp he)
      have hle : zpowers (a ^ 5) ≤ zpowers q := by
        apply IsCyclic.subgroup_le_iff_card_dvd.mpr
        rw [Nat.card_zpowers,Nat.card_zpowers,orderOf_pow,ha,he]
        norm_num
        omega
      have hqstab : zpowers q ≤ stabilizer A x := zpowers_le.mpr hqx
      exact hx ((hle.trans hqstab) (mem_zpowers (a ^ 5))))
  rw [hAcard] at hd
  exact hd

private theorem order_ne_twentyFive
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) : orderOf g ≠ 25 := by
  intro hg
  have hp : orderOf (g ^ 5) = 5 := by rw [orderOf_pow,hg]; norm_num
  have hc := Degree72FiveActual.fixed_card_cases P hcard h5 hnotAlt (g ^ 5) hp
  have hd := twentyFive_dvd_complement (X := X) g hg
  rw [Nat.card_eq_fintype_card (α := X),hcard,← Nat.card_coe_set_eq] at hd
  change 25 ∣ 72 - Nat.card (Function.fixedPoints (g ^ 5).val) at hd
  rcases hc with hc | hc <;> rw [hc] at hd <;> norm_num at hd

theorem pow_five_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (he : ∃ e : ℕ, orderOf g = 5 ^ e) : g ^ 5 = 1 := by
  obtain ⟨e,he⟩ := he
  have hele : e ≤ 1 := by
    by_contra hn
    have hd : 25 ∣ orderOf g := by rw [he]; exact pow_dvd_pow 5 (by omega : 2 ≤ e)
    have hne : orderOf g ≠ 0 := by rw [he]; exact pow_ne_zero _ (by norm_num)
    exact order_ne_twentyFive P hcard h5 hnotAlt (g ^ (orderOf g / 25))
      (orderOf_pow_orderOf_div hne hd)
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [he]
  simpa only [pow_one] using pow_dvd_pow 5 hele

end FiveTransitive.Degree72ThreeFivePower

end CFSG

module

public import CFSG.Permutation.FiveTransitive.ThreeGroupSmallFiveAction
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG

namespace FiveTransitive.ThreeGroupNineNormalizer

open MulAction

theorem card_le_eighty_one
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 9)
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 3 Q) : Nat.card Q ≤ 81 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hd := Subgroup.card_subgroup_dvd_card Q
  rw [Nat.card_perm,hY] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he4 : e ≤ 4 := by
    by_contra hn
    have h243 : 243 ∣ Nat.card Q := by
      rw [he]
      exact pow_dvd_pow 3 (by omega : 5 ≤ e)
    have hh := h243.trans hd
    norm_num [Nat.factorial] at hh
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 3) he4).trans (by norm_num)

private theorem eq_one
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 9)
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 3 Q)
    (htrans : IsPretransitive Q Y)
    (z : (Subgroup.normalizer (Q : Set (Equiv.Perm Y)))) (hz : z ^ 5 = 1) : z = 1 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : IsPretransitive Q Y := htrans
  let N := Subgroup.normalizer (Q : Set (Equiv.Perm Y))
  let _ : MulDistribMulAction N Q := MulDistribMulAction.compHom Q Q.normalizerMonoidHom
  let A := Subgroup.zpowers z
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hz)
  have hmod : Nat.card Y % 5 = Nat.card (fixedPoints A Y) % 5 :=
    hA.card_modEq_card_fixedPoints Y
  rw [hY] at hmod
  obtain ⟨x,hx⟩ := (Nat.card_pos_iff.mp (show 0 < Nat.card (fixedPoints A Y) by omega)).1
  have hcompat : ∀ (a : A) (q : Q) (y : Y), a • (q • y) = (a • q) • (a • y) := by
    intro a q y
    change a.val.val • ((q : Equiv.Perm Y) • y) =
      (Q.normalizerMonoidHom a.val q : Equiv.Perm Y) • (a.val.val • y)
    rw [Q.normalizerMonoidHom_apply_apply_coe,mul_smul,mul_smul,inv_smul_smul]
  have htrivial : ∀ (a : A) (q : Q), a • q = q := by
    by_contra hn
    push Not at hn
    have hbound := card_le_eighty_one hY Q hQ
    have h81 := (ThreeGroupSmallFiveAction.card_and_fixed hA hQ hbound hn).1
    have hindex := index_stabilizer_of_transitive Q x
    have hcard := (stabilizer Q x).card_mul_index
    rw [hindex,hY,h81] at hcard
    have hstab : Nat.card (stabilizer Q x) = 9 := by omega
    have hne : stabilizer Q x ≠ ⊥ := by
      intro he
      rw [he,Subgroup.card_bot] at hstab
      omega
    have htop := ThreeGroupSmallFiveAction.invariant_eq_top hA hQ hbound hn
      (stabilizer Q x) hne (by
        intro a q hq
        change (a • q) • x = x
        change q • x = x at hq
        have hh := hcompat a q x
        rw [hx a,hq,hx a] at hh
        exact hh.symm)
    rw [htop,Subgroup.card_top,h81] at hstab
    omega
  apply Subtype.ext
  apply Equiv.ext
  intro y
  change z.val y = y
  obtain ⟨q,hqy⟩ := htrans.exists_smul_eq x y
  have hh := hcompat (⟨z,Subgroup.mem_zpowers z⟩ : A) q x
  rw [htrivial,hx] at hh
  change z.val (q • x) = q • x at hh
  simpa only [hqy] using hh

theorem perm_eq_one
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 9)
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 3 Q)
    (htrans : IsPretransitive Q Y)
    (z : Equiv.Perm Y) (hzN : z ∈ (Subgroup.normalizer (Q : Set (Equiv.Perm Y)))) (hz : z ^ 5 = 1) : z = 1 := by
  exact congrArg Subtype.val (eq_one hY Q hQ htrans ⟨z,hzN⟩ (Subtype.ext hz))

end FiveTransitive.ThreeGroupNineNormalizer

end CFSG

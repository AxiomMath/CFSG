module

public import CFSG.Permutation.FiveTransitive.Degree48SevenAut
public import Mathlib.Data.Finite.Perm

public section

namespace CFSG

namespace FiveTransitive.Degree54SevenNormalizerSeven

open MulAction

private theorem card_le_seven
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 7)
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 7 Q) : Nat.card Q ≤ 7 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hd := Subgroup.card_subgroup_dvd_card Q
  rw [Nat.card_perm,hY] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have h49 : 49 ∣ Nat.card Q := by
      rw [he]
      exact pow_dvd_pow 7 (by omega : 2 ≤ e)
    have hh := h49.trans hd
    norm_num [Nat.factorial] at hh
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 7) he1).trans (by norm_num)

private theorem eq_one
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 7)
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 7 Q)
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
    intro a q
    exact Degree48SevenAut.smul_eq hA hQ (by
      have hb := card_le_seven hY Q hQ
      omega) a q
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
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 7)
    (Q : Subgroup (Equiv.Perm Y)) (hQ : IsPGroup 7 Q)
    (htrans : IsPretransitive Q Y)
    (z : Equiv.Perm Y) (hzN : z ∈ (Subgroup.normalizer (Q : Set (Equiv.Perm Y)))) (hz : z ^ 5 = 1) : z = 1 := by
  exact congrArg Subtype.val (eq_one hY Q hQ htrans ⟨z,hzN⟩ (Subtype.ext hz))

end FiveTransitive.Degree54SevenNormalizerSeven

end CFSG

module

public import CFSG.Permutation.FiveTransitive.ThreeGroupSmallFiveAction

public section

namespace CFSG

namespace FiveTransitive.SmallThreeNormalizerFiveCentralizes

open MulAction

theorem centralizes_of_fixed_three_orbit
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : IsPGroup 3 Q) (hcard : Nat.card Q ≤ 81)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (x : X) (hx : g.val • x = x) (hOrbit : Nat.card (orbit Q x) = 3) :
    ∀ q : Q, g.val * q.val = q.val * g.val := by
  classical
  let N := Subgroup.normalizer (Q : Set G)
  let _ : MulDistribMulAction N Q := MulDistribMulAction.compHom Q Q.normalizerMonoidHom
  let A := Subgroup.zpowers g
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,pow_one]
    exact orderOf_dvd_of_pow_eq_one hg)
  have hxA (a : A) : a • x = x := by
    have hle : A ≤ stabilizer N x := Subgroup.zpowers_le.mpr hx
    exact hle a.property
  have hcompat : ∀ (a : A) (q : Q) (y : X), a • (q • y) = (a • q) • (a • y) := by
    intro a q y
    change a.val.val • ((q : G) • y) =
      (Q.normalizerMonoidHom a.val q : G) • (a.val.val • y)
    rw [Q.normalizerMonoidHom_apply_apply_coe,mul_smul,mul_smul,inv_smul_smul]
  have htrivial : ∀ (a : A) (q : Q), a • q = q := by
    by_contra hn
    push Not at hn
    have h81 := (ThreeGroupSmallFiveAction.card_and_fixed hA hQ hcard hn).1
    have hindex : (stabilizer Q x).index = 3 := by
      rw [index_stabilizer,← Nat.card_coe_set_eq]
      exact hOrbit
    have hc := (stabilizer Q x).card_mul_index
    rw [hindex,h81] at hc
    have hstab : Nat.card (stabilizer Q x) = 27 := by omega
    have hne : stabilizer Q x ≠ ⊥ := by
      intro he
      rw [he,Subgroup.card_bot] at hstab
      omega
    have htop := ThreeGroupSmallFiveAction.invariant_eq_top hA hQ hcard hn
      (stabilizer Q x) hne (by
        intro a q hq
        change (a • q) • x = x
        change q • x = x at hq
        have hh := hcompat a q x
        rw [hxA a,hq,hxA a] at hh
        exact hh.symm)
    rw [htop,Subgroup.card_top,h81] at hstab
    omega
  intro q
  have hh := congrArg Subtype.val (htrivial (⟨g,Subgroup.mem_zpowers g⟩ : A) q)
  change g.val * q.val * g.val⁻¹ = q.val at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

end FiveTransitive.SmallThreeNormalizerFiveCentralizes

end CFSG

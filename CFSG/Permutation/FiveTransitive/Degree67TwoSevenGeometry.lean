module

public import CFSG.Permutation.FiveTransitive.Degree67TwoSevenFiveLift
public import CFSG.Permutation.FiveTransitive.Degree67TwoSevenOrbit
public import CFSG.Permutation.FiveTransitive.OrbitFixedComplementBound
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoSevenGeometry

open MulAction FixedNormalizerAction NormalizerOrbitFamily

private theorem orbit_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 67) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hfixed : 5 ≤ Nat.card (fixedPoints Q X)) (O : orbitRel.Quotient Q X) :
    Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 ∨
      Nat.card O.orbit = 8 ∨ Nat.card O.orbit = 16 ∨ Nat.card O.orbit = 32 := by
  refine Quotient.inductionOn O ?_
  intro x
  rw [orbitRel.Quotient.orbit_mk]
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := OrbitFixedComplementBound.card_le (G := Q) x
  rw [hX] at hb
  have he5 : e ≤ 5 := by
    by_contra hn
    have hp : 64 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ e)
    omega
  rw [he]
  interval_cases e <;> norm_num

theorem orbits_le_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (hAlt : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q)
    (hfive : ∀ g : P, orderOf g = 5 → Nat.card (Function.fixedPoints g.val) = 2)
    (hseven : ∀ g : P, orderOf g = 7 → Nat.card (Function.fixedPoints g.val) = 4)
    (x : X) : Nat.card (orbit Q x) ≤ 4 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hX : Nat.card X = 67 := by rwa [Nat.card_eq_fintype_card]
  have hfixed : Nat.card (fixedPoints Q X) = 7 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  obtain ⟨g,hg,hfree⟩ := Degree67TwoSevenFiveLift.exists_five_free_exterior P Q hF hAlt hfive
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hd8 := five_dvd_card_family Q g hg5 hfree 8 (by decide) (by decide)
  have hd16 := five_dvd_card_family Q g hg5 hfree 16 (by decide) (by decide)
  have hd32 := five_dvd_card_family Q g hg5 hfree 32 (by decide) (by decide)
  have hb8 := card_mul_le (X := X) Q 8
  have hb16 := card_mul_le (X := X) Q 16
  have hb32 := card_mul_le (X := X) Q 32
  rw [hX] at hb8 hb16 hb32
  have h16 : Nat.card (Family (X := X) Q 16) = 0 := by omega
  have h32 : Nat.card (Family (X := X) Q 32) = 0 := by omega
  have h8 : Nat.card (Family (X := X) Q 8) = 0 := by
    by_contra hn
    have hc8 : Nat.card (Family (X := X) Q 8) = 5 := by omega
    let F := Fixed (X := X) Q
    let N := Normalizer Q
    let _ : Fintype F := Fintype.ofFinite _
    let rho : N →* Equiv.Perm F := MulAction.toPermHom N F
    change alternatingGroup F ≤ rho.range at hAlt
    have hdiv : 7 ∣ Nat.card rho.range :=
      (SylowFixedActionCore.odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7)
        (by decide) (by rw [← Nat.card_eq_fintype_card]; exact hF.ge)).trans
          (Subgroup.card_dvd_of_le hAlt)
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
      (hdiv.trans (Subgroup.card_range_dvd rho))
    have hz7 : z ^ 7 = 1 := hz ▸ pow_orderOf_eq_one z
    have hglobal := hseven z.val ((Subgroup.orderOf_coe z).trans hz)
    let B := Family (X := X) Q 8
    have hex (O : B) : ∃ y : X, y ∈ O.val.orbit ∧ z.val • y = y := by
      have hpres := Degree67TwoSevenOrbit.seven_fixes_family Q 8 (by omega) z hz7 O
      exact Degree67TwoSevenOrbit.exists_fixed_of_preserved Q z hz7 O.val hpres
        (by rw [O.property]; decide)
    let f : B → Function.fixedPoints z.val.val := fun O =>
      ⟨(hex O).choose,(hex O).choose_spec.2⟩
    have hf : Function.Injective f := by
      intro A B h
      have he : (hex A).choose = (hex B).choose := congrArg Subtype.val h
      have ha := orbitRel.Quotient.mem_orbit.mp (hex A).choose_spec.1
      have hb := orbitRel.Quotient.mem_orbit.mp (hex B).choose_spec.1
      exact Subtype.ext (ha.symm.trans ((congrArg Quotient.mk'' he).trans hb))
    have hh := Nat.card_le_card_of_injective f hf
    change Nat.card (Family (X := X) Q 8) ≤ Nat.card (Function.fixedPoints z.val.val) at hh
    omega
  have hc := orbit_card_cases hX Q hQ (by omega) (Quotient.mk'' x)
  have hnot (m : ℕ) (hm : Nat.card (Family (X := X) Q m) = 0) :
      Nat.card (orbit Q x) ≠ m := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q m) :=
      Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩⟩
    omega
  have hn8 := hnot 8 h8
  have hn16 := hnot 16 h16
  have hn32 := hnot 32 h32
  rw [orbitRel.Quotient.orbit_mk] at hc
  omega

end FiveTransitive.Degree67TwoSevenGeometry

end CFSG

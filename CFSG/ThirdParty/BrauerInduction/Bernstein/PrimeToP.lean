module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.Ideal
public import CFSG.ThirdParty.BrauerInduction.Elementary.LocalSum

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Bernstein's prime-to-`p` local sum

This file develops the direct integral form of Bernstein's fixed-prime
argument.

For a `p`-regular element `a` and a commuting `p`-singular element `s`, the
value of `PElementary.f p a` at `a * s` is a fixed-coset count. The fixed-point
congruence shows that this value is not divisible by `p`.

Summing the local functions over the `p`-regular conjugacy classes gives
`PElementary.localSum p`. Its value at every group element is an integer not
divisible by `p`, and the corresponding element of the integral cyclotomic
character ring belongs to Bernstein's fixed-prime ideal `JIdeal p`.

No localization at `p` is used in this file.
-/

universe u v

open scoped BigOperators

namespace CFSG.BrauerInduction.Bernstein

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G] [Finite G]
variable (p : ℕ) [Fact p.Prime]

open PElementary Subgroup in
/--
For a `p`-regular element `a` and a commuting `p`-singular element `s`,
the value of `PElementary.f p a` at `a * s` is an integer not divisible
by `p`.
-/
lemma f_apply_mul_pSingular_not_dvd
    {a : G} (ha : IsPRegular p a)
    (s : G) (hs : IsPSingular p s)
    (hcomm : Commute a s) :
    ∃ n : ℤ,
      PElementary.f (k := k) p a (a * s) = (n : k) ∧
      ¬ (p : ℤ) ∣ n := by
  let C : Subgroup G :=
    centralizer ({a} : Set G)
  let H : Subgroup C :=
    PElementary.P_in_Z p a
  let sC : C :=
    ⟨s, by
      simpa [C, Subgroup.mem_centralizer_iff] using hcomm.eq⟩

  have hsC : IsPSingular p sC := by
    dsimp [IsPSingular] at hs ⊢
    obtain ⟨r, hr⟩ := hs
    refine ⟨r, ?_⟩
    have hord : orderOf sC = orderOf s :=
      (Subgroup.orderOf_coe sC).symm
    rw [hord]
    exact hr

  have hmod :
      Nat.card {c : C ⧸ H // sC • c = c} ≡
        Nat.card (C ⧸ H) [MOD p] :=
    PElementary.card_fixedPoints_pSingular_modEq H sC hsC

  letI : Fintype C := Fintype.ofFinite C
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (PElementary.P_of_Z p a) :=
    Fintype.ofFinite (PElementary.P_of_Z p a)

  have hHcard :
      Fintype.card (PElementary.P_of_Z p a) =
        Fintype.card H := by
    symm
    apply Fintype.card_congr
    exact
      (Subgroup.equivMapOfInjective
        _ _ Subtype.coe_injective).toEquiv

  have hquotient :
      Nat.card (C ⧸ H) = PElementary.index p a := by
    unfold PElementary.index
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
    simp only [Nat.card_eq_fintype_card]
    rw [hHcard, Nat.mul_div_cancel]
    exact Fintype.card_pos

  have hquotient_not_dvd :
      ¬ p ∣ Nat.card (C ⧸ H) := by
    rw [hquotient]
    simpa [PElementary.index] using
      PElementary.p_not_dvd_cardCentralizer_div_cardP
        (p := p) a

  have heval :
      PElementary.f (k := k) p a (a * s) =
        (Nat.card {c : C ⧸ H // sC • c = c} : k) := by
    simpa [C, H, sC] using
      f_apply_mul_pSingular_eq_card_fixedCosets
        (k := k) p ha s hs hcomm

  refine
    ⟨(Nat.card {c : C ⧸ H // sC • c = c} : ℤ),
      ?_, ?_⟩
  · simpa using heval
  · intro hfixed_dvd

    have hquotient_not_dvd_int :
        ¬ (p : ℤ) ∣ (Nat.card (C ⧸ H) : ℤ) := by
      simpa only [Int.ofNat_dvd] using hquotient_not_dvd

    apply hquotient_not_dvd_int

    have hdiff :
        (p : ℤ) ∣
          (Nat.card (C ⧸ H) : ℤ) -
            (Nat.card {c : C ⧸ H // sC • c = c} : ℤ) := by
      apply Int.ModEq.dvd
      exact Int.natCast_modEq_iff.mpr hmod

    have hsum :=
      dvd_add hdiff hfixed_dvd

    simpa using hsum

/--
If `a` is conjugate to the `p`-regular part of `g`, then the value of
`PElementary.f p a` at `g` is an integer not divisible by `p`.
-/
lemma f_apply_not_dvd_of_isConj_pRegular
    {a g : G}
    (ha : IsPRegular p a)
    (hconj : IsConj a (Group.pRegular p g)) :
    ∃ n : ℤ,
      PElementary.f (k := k) p a g = (n : k) ∧
      ¬ (p : ℤ) ∣ n := by
  let r := Group.pRegular p g
  let s := Group.pSingular p g

  have hgfin : IsOfFinOrder g :=
    isOfFinOrder_of_finite g

  have hdecomp : g = r * s :=
    (Group.pDecomp' p hgfin).symm

  have hs : IsPSingular p s :=
    Group.isPSingular_pSingular p g

  have hrs : Commute r s :=
    Group.pRegular_pSingular_commute p rfl

  obtain ⟨x, hx⟩ :=
    isConj_iff.mp hconj

  have hx' : r = x * a * x⁻¹ := by
    simpa [r] using hx.symm

  let s' := x⁻¹ * s * x

  have hs' : IsPSingular p s' := by
    dsimp [s']
    exact IsPSingular.conj' p hs x

  have hs'_comm : Commute a s' := by
    have ha_eq :
        a = x⁻¹ * r * x := by
      calc
        a = x⁻¹ * (x * a * x⁻¹) * x := by group
        _ = x⁻¹ * r * x := by rw [hx]

    rw [ha_eq]
    dsimp [s']

    calc
      (x⁻¹ * r * x) * (x⁻¹ * s * x)
          =
        x⁻¹ * (r * s) * x := by group
      _ =
        x⁻¹ * (s * r) * x := by rw [hrs.eq]
      _ =
        (x⁻¹ * s * x) * (x⁻¹ * r * x) := by group

  have hg_conj :
      IsConj g (a * s') := by
    rw [isConj_iff]
    refine ⟨x⁻¹, ?_⟩
    simp only [inv_inv]
    rw [hdecomp, hx']
    dsimp [s']
    group

  obtain ⟨n, hn, hn_not_dvd⟩ :=
    f_apply_mul_pSingular_not_dvd
      (k := k) p ha s' hs' hs'_comm

  refine ⟨n, ?_, hn_not_dvd⟩

  calc
    PElementary.f (k := k) p a g
        =
      PElementary.f (k := k) p a (a * s') :=
        ClassFun.apply_eq_apply_of_isConj hg_conj
    _ = (n : k) := hn

/--
At every group element, the fixed-prime local sum has an integer value not
divisible by `p`.

This is Bernstein's direct fixed-prime conclusion.
-/
lemma localSum_apply_not_dvd
    (g : G) :
    ∃ n : ℤ, PElementary.localSum p g = (n : k) ∧ ¬ (p : ℤ) ∣ n := by
  let r := Group.pRegular p g

  have hr : IsPRegular p r :=
    Group.isPRegular_pRegular p
      (isOfFinOrder_of_finite g)

  obtain ⟨C, hC, hC_unique⟩ :=
    PRegularClass.unique_of_isPRegular p r hr

  obtain ⟨n, hn, hn_not_dvd⟩ :=
    f_apply_not_dvd_of_isConj_pRegular
      (k := k) p
      (PRegularClass.repr_isPRegular C)
      hC

  refine ⟨n, ?_, hn_not_dvd⟩

  calc
    PElementary.localSum (k := k) p g
        =
      PElementary.f (k := k) p C.repr g := by
        classical
        simp only [
          PElementary.localSum,
          ClassFun.sum_apply
        ]
        rw [Finset.sum_eq_single C]
        · intro D _ hDC
          apply PElementary.f_apply_eq_zero_of_not_isConj
          intro h
          exact hDC (hC_unique D h.symm)
        · intro hC_not_mem
          exact (hC_not_mem (Finset.mem_univ C)).elim
    _ = (n : k) := hn

/--
The fixed-prime local sum belongs to Bernstein's integral span `J p`.
-/
lemma localSum_mem_J [IsAlgClosed k] :
    PElementary.localSum p ∈ J (k := k) (G := G) p := by
  unfold PElementary.localSum
  apply Submodule.sum_mem
  intro C _
  exact
    f_a_mem_J (k := k) p C.repr
      (PRegularClass.repr_isPRegular C)


/--
The fixed-prime local sum belongs to Bernstein's fixed-prime ideal.
-/
lemma localSumElement_mem_JIdeal [IsAlgClosed k] :
    PElementary.localSumElement (k := k) (G := G) p ∈ JIdeal p := by
  change
    PElementary.localSum (k := k) p ∈ J p
  exact localSum_mem_J p

end Bernstein

end CFSG.BrauerInduction

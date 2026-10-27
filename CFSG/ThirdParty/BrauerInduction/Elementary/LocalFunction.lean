module

public import CFSG.ThirdParty.BrauerInduction.Elementary.FourierDelta

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Local functions induced from associated p-elementary subgroups

For a prime `p` and a `p`-regular element `a`, this file defines the class
function obtained by inducing the Fourier delta function on the associated
subgroup `E(a)`.

It proves the support property of this function and computes its value at `a`
as the prime-to-`p` index of the chosen Sylow subgroup in the centralizer of
`a`.
-/

universe u v

open ClassFun

namespace CFSG.BrauerInduction
namespace PElementary

section LocalFunction

variable (p : ℕ) [Fact p.Prime]
variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/-!
## The induced class function `f` and its support

This section defines `f p a = Ind_{E(a)}^G (phi p k a)` and proves the basic
support statement: `f p a x` vanishes when the `p`-regular part of `x` is not
conjugate to `a`.
-/

variable (p : ℕ)
variable {k : Type u} [Field k]
variable {G : Type v} [Group G] [Fact p.Prime]

/-- Bernstein Step 8: the induced class function `f`, denoted `f_a` in the proof. -/
@[expose] noncomputable def f [Finite G]
    (a : G) : ClassFun k G :=
  ClassFun.ind (k := k)  (E_subgroup p a)  (phi p k a)

/-- Bernstein Step 8, Claim (ii), support part.

If the `p`-regular part of `x` is not conjugate to `a`, then the induced function
`f` vanishes at `x`.
-/
lemma f_apply_eq_zero_of_not_isConj [Finite G]
    (a x : G)
    (hx : ¬ IsConj (Group.pRegular p x) a) :
    f (k := k) p a x = 0 := by
  unfold f
  rw [ClassFun.ind_apply]

  apply Finset.sum_eq_zero
  intro q hq

  by_cases hE : q.out⁻¹ * x * q.out ∈ E_subgroup p a
  · have hne :
        Group.pRegular p (q.out⁻¹ * x * q.out) ≠ a := by
      intro hpreg_eq
      apply hx
      have hpreg_conj :
          Group.pRegular p (q.out⁻¹ * x * q.out)
            =
          q.out⁻¹ * Group.pRegular p x * q.out := by
        simp only [Group.pRegular_conj']
      have hconj_eq :
          q.out⁻¹ * Group.pRegular p x * q.out = a := by
        rw [← hpreg_conj]
        exact hpreg_eq
      rw [isConj_iff]
      refine ⟨q.out⁻¹, ?_⟩
      rw [inv_inv]
      exact hconj_eq
    simp only [hE, ↓reduceDIte, phi, ClassFun.coe_mk, hne, ↓reduceIte]

  · simp [hE]

/--
For a `p`-regular element `a`, the conjugate `x⁻¹ * a * x` contributes
nontrivially to `phi p k a` exactly when `x` centralizes `a`.
-/
lemma conj_inv_mem_E_and_phi_nonzero_iff [Finite G]
    {a : G} (ha : IsPRegular p a) (x : G) :
    (x⁻¹ * a * x ∈ E_subgroup p a ∧
        Group.pRegular p (x⁻¹ * a * x) = a)
      ↔ x ∈ Subgroup.centralizer ({a} : Set G) := by
  constructor
  · rintro ⟨hxE, hreg⟩
    have hf : IsOfFinOrder a := isOfFinOrder_of_finite a
    have hpreg_conj :
        Group.pRegular p (x⁻¹ * a * x)
          =
        x⁻¹ * Group.pRegular p a * x := by
      simp only [Group.pRegular_conj']
    have hpreg_a :
        Group.pRegular p a = a :=
      Group.pRegular_eq_self_of_isPRegular p hf ha

    have hx_conj_a :
        x⁻¹ * a * x = a := by
      calc
        x⁻¹ * a * x
          = x⁻¹ * Group.pRegular p a * x := by rw [hpreg_a]
        _ = Group.pRegular p (x⁻¹ * a * x) := by rw [hpreg_conj]
        _ = a := hreg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    · calc
        a * x
          = x * (x⁻¹ * a * x) := by group
        _ = x * a := by rw [hx_conj_a]
  · intro hxC
    have h_comm : x * a = a * x := by
      exact Eq.symm (SemiconjBy.eq (hxC a rfl))
    have h_eq : x⁻¹ * a * x = a := by
      calc
        x⁻¹ * a * x = x⁻¹ * (a * x) := by group
        _ = x⁻¹ * (x * a) := by rw [← h_comm]
        _ = a := by group
    refine ⟨?_, ?_⟩
    · rw [h_eq]
      apply Subgroup.mem_sup_left
      exact Subgroup.mem_zpowers a
    · rw [h_eq]
      exact Group.pRegular_eq_self_of_isPRegular p (isOfFinOrder_of_finite a) ha

/-!
## Evaluation of `f` at `a`

This section computes `f(a)`.  The result is expressed as Bernstein's index,
the index of the chosen Sylow `p`-subgroup in the centralizer of `a`, and is
shown to be prime to `p`.
-/

variable (p : ℕ) [Fact p.Prime]
variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
Closed formula for `f(a)` in terms of the centralizer of `a`, the subgroup
`E(a)`, and `orderOf a`.
-/
lemma f_apply_a_closed_form
    [CharZero k] [Finite G]
    {a : G} (ha : IsPRegular p a) :
    f (k := k) p a a
      =
    (Nat.card (E_subgroup p a) : k)⁻¹
      * (Nat.card (Subgroup.centralizer ({a} : Set G)) : k)
      * (orderOf a : k) := by
  classical
  letI: Fintype G := Fintype.ofFinite G
  unfold f
  rw [ClassFun.ind_apply_eq_inv_mul_sum]
  dsimp [phi]

  have h_integrand :
      (fun x : G =>
        if hx : x⁻¹ * a * x ∈ E_subgroup p a then
          if Group.pRegular p (x⁻¹ * a * x) = a
          then (orderOf a : k)
          else 0
        else 0)
      =
      (fun x : G =>
        if x ∈ Subgroup.centralizer ({a} : Set G)
        then (orderOf a : k)
        else 0) := by
    ext x
    by_cases hxC : x ∈ Subgroup.centralizer ({a} : Set G)
    · have hxBoth :
          x⁻¹ * a * x ∈ E_subgroup p a ∧
            Group.pRegular p (x⁻¹ * a * x) = a :=
        (conj_inv_mem_E_and_phi_nonzero_iff
          p ha x).mpr hxC
      rcases hxBoth with ⟨hxE, hreg⟩
      rw [dif_pos hxE, if_pos hreg, if_pos hxC]
    · have hxNotBoth :
          ¬ (x⁻¹ * a * x ∈ E_subgroup p a ∧
              Group.pRegular p (x⁻¹ * a * x) = a) :=
        mt (conj_inv_mem_E_and_phi_nonzero_iff
          p ha x).mp hxC

      by_cases hxE : x⁻¹ * a * x ∈ E_subgroup p a
      · have hreg_not :
            Group.pRegular p (x⁻¹ * a * x) ≠ a := by
          intro hreg
          exact hxNotBoth ⟨hxE, hreg⟩
        rw [dif_pos hxE, if_neg hreg_not, if_neg hxC]
      · rw [dif_neg hxE, if_neg hxC]

  have hsum :=
    congrArg
      (fun F : G → k =>
        (Nat.card (E_subgroup p a) : k)⁻¹ * ∑ x : G, F x)
      h_integrand
  rw [hsum]

  rw [Subgroup.sum_ite_mem_centralizer_mul]
  ring_nf

/--
Bernstein's index attached to `a`: the index of the chosen Sylow `p`-subgroup
inside the centralizer of `a`.
-/
@[expose] noncomputable def index (x : G) : ℕ :=
  Nat.card (Subgroup.centralizer
    ({x} : Set G)) / Nat.card (P_of_Z  p x)

open Subgroup in
/--
The value of `f p a` at `a` is Bernstein's index: the index of the
chosen Sylow `p`-subgroup `P_Z(a)` inside the centralizer of `a`.
-/
lemma f_apply_a_eq_index
    [CharZero k] [Finite G]
    {a : G} (ha : IsPRegular p a) :
    f p a a = (index p a : k) := by
  rw [f_apply_a_closed_form p ha]
  have hE_card : Nat.card (E_subgroup p a) = orderOf a * Nat.card (P_of_Z  p a) := E_card p ha
  have hC_card : Nat.card (centralizer ({a} : Set G)) =
      index p a * Nat.card (P_of_Z  p a) := by
    have h_dvd : Nat.card (P_of_Z  p a) ∣ Nat.card (centralizer ({a} : Set G)) := by
      rw [card_P_of_Z_eq_card_P_in_Z a]
      exact card_subgroup_dvd_card (P_in_Z p a : Subgroup (centralizer ({a} : Set G)))
    rw [index, Nat.div_mul_cancel h_dvd]
  have h_kE : (Nat.card (E_subgroup p a) : k) =
      (orderOf a : k) * (Nat.card (P_of_Z  p a) : k) := by
    rw [hE_card, Nat.cast_mul]
  have h_kC : (Nat.card (centralizer ({a} : Set G)) : k)
      = (index  p a : k) * (Nat.card (P_of_Z  p a) : k) := by
    rw [hC_card, Nat.cast_mul]
  rw [h_kE, h_kC]
  have h_ord_ne_zero : (orderOf a : k) ≠ 0 := Nat.cast_ne_zero.mpr (orderOf_pos a).ne'
  have h_P_ne_zero : (Nat.card (P_of_Z  p a) : k) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  calc ((orderOf a : k) * (Nat.card (P_of_Z  p a) : k))⁻¹ * ((index p a : k) *
          (Nat.card (P_of_Z  p a) : k)) * (orderOf a : k)
    _ = (orderOf a : k)⁻¹ * (Nat.card (P_of_Z  p a) : k)⁻¹ * ((index p a : k) *
          (Nat.card (P_of_Z  p a) : k)) * (orderOf a : k) := by rw [mul_inv]
    _ = (index p a : k) * ((Nat.card (P_of_Z  p a) : k)⁻¹ * (Nat.card (P_of_Z  p a) : k))
          * ((orderOf a : k)⁻¹ * (orderOf a : k)) := by ring
    _ = (index p a : k) * 1 * 1 :=
        by rw [inv_mul_cancel₀ h_P_ne_zero, inv_mul_cancel₀ h_ord_ne_zero]
    _ = (index p a : k) :=
        by ring

lemma f_apply_self_coprime
    [CharZero k] [Finite G]
    {a : G} (ha : IsPRegular p a) :
    ∃ n : ℤ,
      f (k := k) p a a = (n : k) ∧
        ¬ (p : ℤ) ∣ n := by
  let n : ℕ := index p a
  refine ⟨(n : ℤ), ?_, ?_⟩
  · rw [f_apply_a_eq_index (k := k) p ha]
    simp [n]
  · rw [Int.ofNat_dvd]
    simpa [n, index] using
      p_not_dvd_cardCentralizer_div_cardP (p := p) (x := a)

end LocalFunction
end CFSG.BrauerInduction.PElementary

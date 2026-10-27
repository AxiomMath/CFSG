module

public import CFSG.ThirdParty.BrauerInduction.Elementary.CyclicCharacters
public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.CharacterSystem
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Fourier delta functions on associated p-elementary subgroups

For a prime `p` and a `p`-regular element `a`, this file defines a class
function on the associated subgroup `E(a)` which is supported on elements
whose `p`-regular part is `a`.

The function is expressed as a finite Fourier sum of linear characters inflated
from the cyclic factor of `E(a)`. Consequently, it is both integer-valued and
contained in the cyclotomic character span `R_Λ(E(a))`.
-/

universe u v

open scoped BigOperators
open ClassFun

namespace CFSG.BrauerInduction
namespace PElementary

section FourierDelta

variable (p : ℕ) [Fact p.Prime]
variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

noncomputable local instance instFintypeRootsOfUnityOrderOf
    {k : Type u} [Field k]
    {G : Type v} [Group G] [Finite G]
    (a : G) :
    Fintype (rootsOfUnity (orderOf a) k) := by
  have hfin : IsOfFinOrder a := isOfFinOrder_of_finite a
  have hne0 : orderOf a ≠ 0 := (orderOf_ne_zero_iff).2 hfin
  haveI : NeZero (orderOf a) := ⟨hne0⟩
  exact Fintype.ofFinite (rootsOfUnity (orderOf a) k)

/--
The Fourier expansion of the delta function `phi`.

The sum ranges over the `orderOf a`-th roots of unity and is a linear
combination of the characters inflated from the cyclic factor of `E(a)`.
-/
noncomputable def phiSum
    {a : G} (ha : IsPRegular p a) :
    ClassFun k (E_subgroup p a) := by
  have haMem : a ∈ E_subgroup p a := by
    refine (le_sup_left : Cyc a ≤ E_subgroup p a) ?_
    refine (Subgroup.mem_zpowers_iff).2 ?_
    exact ⟨(1 : ℤ), by simp⟩
  have haInvMem : a⁻¹ ∈ E_subgroup p a :=
    (E_subgroup p a).inv_mem haMem
  have hfin : IsOfFinOrder a := IsPRegular.isOfFinOrder p ha
  have hne0 : orderOf a ≠ 0 := (orderOf_ne_zero_iff).2 hfin
  haveI : NeZero (orderOf a) := ⟨hne0⟩
  letI : Fintype (rootsOfUnity (orderOf a) k) :=
    Fintype.ofFinite (rootsOfUnity (orderOf a) k)
  exact
    ∑ ζ : rootsOfUnity (orderOf a) k,
      (((psiEZeta p ha ζ) ⟨a⁻¹, haInvMem⟩ : kˣ) : k)
        • ClassFun.character (VpsiEZeta p ha ζ)

/--
Pointwise expansion of `phiSum` as a sum of scalar multiples of linear
characters.
-/
lemma phiSum_apply_expand [Finite G]
    {a : G}
    (ha : IsPRegular p a)
    (x : E_subgroup p a) :
    phiSum p ha x =
      ∑ ζ : rootsOfUnity (orderOf a) k,
        (((psiEZeta  (k := k) p ha ζ)
            ⟨a⁻¹, inv_mem_E_subgroup (p := p) a⟩ : kˣ) : k) *
          (((psiEZeta  (k := k) p ha ζ) x : kˣ) : k) := by
  simp only [phiSum, VpsiEZeta, FDRep.ofLinearChar,
    ClassFun.char_apply, ClassFun.sum_apply, ClassFun.smul_apply]
  apply Finset.sum_congr rfl
  intro ζ hζ
  congr 1
  simpa [FDRep.ofLinearChar] using
    FDRep.char_ofLinearChar (psiEZeta p ha ζ) x

/--
In the pointwise expansion of `phiSum`, the two values of the linear character
combine to the value at the product `a⁻¹ * x`.
-/
lemma phiSum_apply_product_eq_combine [Finite G]
    {a : G} (ha : IsPRegular p a)
    (x : E_subgroup p a) :
    (∑ ζ : rootsOfUnity (orderOf a) k,
        (((psiEZeta p ha ζ)
            ⟨a⁻¹, inv_mem_E_subgroup p a⟩ : kˣ) : k) *
          (((psiEZeta p ha ζ) x : kˣ) : k))
      =
    ∑ ζ : rootsOfUnity (orderOf a) k,
        (((psiEZeta p ha ζ)
            (⟨a⁻¹, inv_mem_E_subgroup p a⟩ * x) : kˣ) : k) := by
  apply Finset.sum_congr rfl
  intro ζ _
  have hmul :
      (psiEZeta p ha ζ)
          (⟨a⁻¹, inv_mem_E_subgroup p a⟩ * x)
        =
      (psiEZeta p ha ζ) ⟨a⁻¹, inv_mem_E_subgroup p a⟩ *
        (psiEZeta p ha ζ) x := by
    exact MonoidHom.map_mul (psiEZeta p ha ζ) ⟨a⁻¹, inv_mem_E_subgroup p a⟩ x
  rw [hmul]
  simp only [Units.val_mul]

/--
If an element of `E(a)` is not in the `P`-part, then the sum of the linear
characters `ψ_ζ` over all roots of unity vanishes.

This is the first point in the construction where the coefficient field is
assumed algebraically closed: the proof uses the full set of `orderOf a`-th
roots of unity and the standard vanishing sum for a nontrivial power of them.
-/
lemma sum_psiEZeta_eq_zero_of_not_mem_P
    [CharZero k] [IsAlgClosed k] [Finite G]
    {a : G} (ha : IsPRegular p a)
    (y : E_subgroup p a)
    (hyP : (y : G) ∉ P_of_Z p a) :
    (∑ ζ : rootsOfUnity (orderOf a) k,
        (((psiEZeta p ha ζ) y : kˣ) : k)) = 0 := by
  let y_G : G := (y : G)
  have hy_H : y_G ∈ Cyc a ⊔ P_of_Z p a := y.property
  let y_sub : ↥(Cyc a ⊔ P_of_Z p a) := ⟨y_G, hy_H⟩

  let H_elem := associatedSubgroup ha
  let iso := mulEquivProd H_elem
  let c_sub := (iso.symm y).1
  let s_sub := (iso.symm y).2

  obtain ⟨n, hn_eq⟩ : ∃ n : ℤ, (c_sub : G) = a ^ n := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp c_sub.property
    exact ⟨n, hn.symm⟩

  have hn_toCyc : ((E_to_Cyc p a ha y : Cyc a) : G) = a ^ n := by
      have hcyc :
          ((E_to_Cyc p a ha y : Cyc a) : G) =
            (c_sub : G) := by
        simp only [E_to_Cyc_apply, E_Cyc_equiv_apply_coe, H_elem, c_sub, iso]
      exact hcyc.trans hn_eq

  have h_ndiv : ¬ (orderOf a : ℤ) ∣ n := by
    intro h_div
    have h_an_one : a ^ n = 1 := orderOf_dvd_iff_zpow_eq_one.mp h_div
    have hc_one : (c_sub : G) = 1 := by rw [hn_eq, h_an_one]
    have h_prod : (c_sub : G) * (s_sub : G) = y_G := by
      have h_eval : (iso (c_sub, s_sub) : G) =
          (c_sub : G) * (s_sub : G) := rfl
      rw [← h_eval]
      exact congrArg Subtype.val (iso.apply_symm_apply y_sub)
    have hy_in_P : y_G ∈ P_of_Z p a := by
      have h_y_eq_u : y_G = (s_sub : G) := by
        calc
          y_G = (c_sub : G) * (s_sub : G) := h_prod.symm
          _ = 1 * (s_sub : G) := by rw [hc_one]
          _ = (s_sub : G) := one_mul _
      rw [h_y_eq_u]
      exact s_sub.property
    exact hyP hy_in_P

  have h_sum :
      (∑ ζ : rootsOfUnity (orderOf a) k,
          (((psiEZeta p ha ζ) y : kˣ) : k))
        =
      ∑ ζ : rootsOfUnity (orderOf a) k,
          (((ζ : kˣ) ^ n : kˣ) : k) := by
    apply Finset.sum_congr rfl
    intro ζ _
    have hn_toCyc : ((E_to_Cyc p a ha y : Cyc a) : G) = a ^ n := by
      simp only [E_to_Cyc_apply, E_Cyc_equiv_apply_coe]
      simpa [E_to_Cyc_apply, E_Cyc_equiv, c_sub] using hn_eq
    rw [psiEZeta_apply_eq_zpow_of_cycPart_eq_zpow
      (k := k) (p := p) ha y hn_toCyc ζ]

  rw [h_sum]
  have:  NeZero (orderOf a) := IsPRegular.neZero_orderOf p ha
  exact rootsOfUnity.sum_zpow_eq_zero_of_not_dvd (orderOf a) n h_ndiv

open Classical in
/--
The Fourier delta function on the associated subgroup `E(a)`.

Its value is `orderOf a` when the `p`-regular part of the argument is `a`,
and zero otherwise.
-/
@[expose] noncomputable def phi
    (k : Type u) [CommRing k] (a : G) :
  ClassFun k (E_subgroup p a) where
  toFun := fun x => if Group.pRegular p (x : G) = a then (orderOf a : k) else 0
  map_conj := by
    intro x y hc
    obtain ⟨g, hg⟩ := hc
    have hy : y = g * x * g⁻¹ := by
      calc y = (y * g) * g⁻¹ := by exact (Units.eq_mul_inv_iff_mul_eq g).mpr rfl
           _ = (g * x) * g⁻¹ := by rw [hg]
           _ = g * x * g⁻¹ := by rw [mul_assoc]
    subst hy
    congr 1
    ext
    push_cast
    have h_conj : Group.pRegular p ((g : G) * (x : G) * (g : G)⁻¹) =
        (g : G) * Group.pRegular p (x : G) * (g : G)⁻¹ := by
      rw [Group.pRegular_conj]
    have h_iff :
      Group.pRegular p ((g : G) * (x : G) * (g : G)⁻¹) = a ↔ Group.pRegular p (x : G) = a := by
      constructor
      · intro h1
        have h2 : Group.pRegular p (x : G) = (g : G)⁻¹ * a * (g : G) := by
          calc Group.pRegular p (x : G)
            _ = (g : G)⁻¹ * ((g : G) * Group.pRegular p (x : G) * (g : G)⁻¹) * (g : G) := by group
            _ = (g : G)⁻¹ * a * (g : G) := by rw [← h_conj, h1]
        rw [h2]
        have h3 := E_commutes_with_a p a g⁻¹
        simp only [Subgroup.coe_inv, inv_inv] at h3
        exact h3
      · intro h1
        rw [h_conj, h1]
        exact E_commutes_with_a p a g
    exact h_iff.symm

open Classical in
@[simp]
lemma phi_apply
    (k : Type u) [CommRing k]
    {a : G} (x : E_subgroup p a) :
    phi  p k a x =
      if Group.pRegular p (x : G) = a then (orderOf a : k) else 0 :=
  rfl

/-- The Fourier delta function is integer-valued. -/
lemma phi_mem_C_Z (a : G)
    (k : Type u) [CommRing k] :
    phi p k a ∈ C_Z k (E_subgroup p a) := by
  intro x
  by_cases h : Group.pRegular p (x : G) = a
  · refine ⟨(orderOf a : ℤ), ?_⟩
    simp [phi, h]
  · refine ⟨0, ?_⟩
    simp [phi, h]

open Classical in
/--
The direct definition of `phi` agrees with its Fourier expansion.
-/
lemma phi_eq_phiSum
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [Finite G]
    {a : G} (ha : IsPRegular p a) :
    phi p k a = phiSum p ha := by
  ext x
  rw [phi_apply p k x]
  rw [phiSum_apply_expand p ha x]
  rw [phiSum_apply_product_eq_combine p ha x]
  let aInvE : E_subgroup p a := ⟨a⁻¹, inv_mem_E_subgroup p a⟩
  haveI : NeZero (orderOf a) := IsPRegular.neZero_orderOf p ha
  by_cases h_reg : Group.pRegular p (x : G) = a
  · have h_in_P :
        ((aInvE * x : E_subgroup p a) : G) ∈ P_of_Z  p a := by
      have h_fiber := (mem_associatedSubgroup_fiber ha x).mp h_reg
      obtain ⟨s, hs_P, h_x_eq⟩ := h_fiber
      have h_ax_eq_s : ((aInvE * x : E_subgroup p a) : G) = s := by
        push_cast
        rw [h_x_eq, inv_mul_cancel_left]
      rw [h_ax_eq_s]
      exact hs_P
    have h_psi_one :
        ∀ ζ : rootsOfUnity (orderOf a) k,
            psiEZeta p ha ζ (aInvE * x) = 1 := by
      intro ζ
      exact psiEZeta_apply_eq_one_of_mem_P
        (k := k) (p := p) ha ζ (aInvE * x) h_in_P
    have hcard :
        Fintype.card (rootsOfUnity (orderOf a) k) = orderOf a := by
      rw [← Nat.card_eq_fintype_card]
      exact HasEnoughRootsOfUnity.natCard_rootsOfUnity k (orderOf a)
    change
      (if Group.pRegular p (x : G) = a then (orderOf a : k) else 0)
        =
      ∑ ζ : rootsOfUnity (orderOf a) k, (((psiEZeta p ha ζ) (aInvE * x) : kˣ) : k)
    simp only [
      h_reg, ↓reduceIte, h_psi_one, Units.val_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one
    ]
    exact_mod_cast hcard.symm
  · have h_not_in_P :
        ((aInvE * x : E_subgroup p a) : G) ∉ P_of_Z p a := by
      intro hyP
      apply h_reg
      have h_fiber := mem_associatedSubgroup_fiber ha x
      apply h_fiber.mpr
      refine ⟨((aInvE * x : E_subgroup p a) : G), hyP, ?_⟩
      change (x : G) = a * (a⁻¹ * (x : G))
      simp only [mul_inv_cancel_left]
    have hsum0 :
        (∑ ζ : rootsOfUnity (orderOf a) k,
          (((psiEZeta p ha ζ) (aInvE * x) : kˣ) : k)) = 0 :=
      sum_psiEZeta_eq_zero_of_not_mem_P
        (k := k) (p := p) ha (aInvE * x) h_not_in_P
    simp only [h_reg, ↓reduceIte]
    exact by
      simpa using hsum0.symm

/-- The Fourier expansion lies in the cyclotomic character span. -/
lemma phiSum_mem_R_Lambda
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Finite G]
    {a : G} (ha : IsPRegular p a) :
    phiSum p ha ∈ R_Lambda k G (E_subgroup p a) := by
  dsimp [phiSum]

  have haMem : a ∈ E_subgroup p a := by
    refine (le_sup_left : Cyc a ≤ E_subgroup p a) ?_
    refine (Subgroup.mem_zpowers_iff).2 ?_
    exact ⟨(1 : ℤ), by simp⟩

  have haInvMem : a⁻¹ ∈ E_subgroup p a :=
    (E_subgroup p a).inv_mem haMem

  change
    (Finset.univ.sum (fun ζ : rootsOfUnity (orderOf a) k =>
      (((psiEZeta p ha ζ) ⟨a⁻¹, haInvMem⟩ : kˣ) : k)
        • ClassFun.character (VpsiEZeta (k := k) p ha ζ)))
      ∈ R_Lambda k G (E_subgroup p a)

  refine Submodule.sum_mem _ ?_
  intro ζ hζ

  let c : Lambda k G :=
    ⟨(((psiEZeta (k := k) p ha ζ) ⟨a⁻¹, haInvMem⟩ : kˣ) : k),
      psiEZeta_apply_a_inv_mem_Lambda
      (k := k) p ha ζ haInvMem⟩

  change
    c • ClassFun.character (VpsiEZeta p ha ζ)
      ∈ R_Lambda k G (E_subgroup p a)

  exact Submodule.smul_mem _ c
    (R_Lambda.char_mem (k := k) (E_subgroup p a) (VpsiEZeta p ha ζ))


/-- The Fourier delta function lies in the cyclotomic character span. -/
 lemma phi_mem_R_Lambda
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Type u} [Group G] [Finite G]
    (a : G) (ha : IsPRegular p a) :
    phi p k a ∈ R_Lambda k G (E_subgroup p a) := by
    have hEq : phi p k a = phiSum p ha := by
      exact phi_eq_phiSum p ha
    simpa [hEq] using (phiSum_mem_R_Lambda p ha)


/--
The Fourier delta function is an integer-valued element of the cyclotomic
character span. -/
lemma phi_mem_Q
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {G : Type u} [Group G] [Finite G]
    (a : G) (ha : IsPRegular p a) :
    phi p k a ∈ Q_sys k G (E_subgroup p a) := by
  exact ⟨
    phi_mem_R_Lambda p a ha,
    phi_mem_C_Z p a k
  ⟩

end FourierDelta
end PElementary
end CFSG.BrauerInduction

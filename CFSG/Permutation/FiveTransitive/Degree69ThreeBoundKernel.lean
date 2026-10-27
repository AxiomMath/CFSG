module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree69ThreeBoundKernel
open MulAction NormalizerOrbitFamily
open scoped BigOperators

theorem exists_kernel
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (hF : Nat.card (fixedPoints Q X) = 6)
    (a : Fin 10 ↪ Family (X := X) Q 3) :
    ∃ R : Subgroup Q, R.index ≤ 3 ^ 10 ∧ ∃ s : Finset X,
      s.card = 36 ∧ ∀ r : R, ∀ x ∈ s, r • x = x := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let xi (i : Fin 10) : X := (a i).val.out
  have hxi (i : Fin 10) : orbit Q (xi i) = (a i).val.orbit :=
    (orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq').symm
  let O (i : Fin 10) : SubMulAction Q X :=
    { carrier := orbit Q (xi i)
      smul_mem' := by
        intro q y hy
        obtain ⟨r,hr⟩ := mem_orbit_iff.mp hy
        exact mem_orbit_iff.mpr ⟨q * r,by rw [mul_smul,hr]⟩ }
  have hO (i : Fin 10) : Nat.card (O i) = 3 := by
    change Nat.card (orbit Q (xi i)) = 3
    rw [hxi]
    exact (a i).property
  let rho : Q →* (∀ i : Fin 10, Equiv.Perm (O i)) :=
    MonoidHom.pi (fun i => MulAction.toPermHom Q (O i))
  let R := rho.ker
  have hindex : R.index ≤ 3 ^ 10 := by
    change rho.ker.index ≤ 3 ^ 10
    rw [Subgroup.index_ker]
    have hgroup := hQ.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective
    obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hgroup
    have hd := Subgroup.card_subgroup_dvd_card rho.range
    have hprod : Nat.card (∀ i : Fin 10, Equiv.Perm (O i)) = (Nat.factorial 3)^10 := by
      simp only [Nat.card_pi,Nat.card_perm,hO,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [hprod,he] at hd
    have he10 : e ≤ 10 := by
      by_contra hn
      have h177147 : 177147 ∣ 3 ^ e := pow_dvd_pow 3 (by omega : 11 ≤ e)
      have hh := h177147.trans hd
      norm_num [Nat.factorial] at hh
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) he10
  have hRfixO (r : R) (i : Fin 10) (y : O i) : r • y.val = y.val := by
    have h := congrFun (show rho r.val = 1 from r.property) i
    exact congrArg Subtype.val (DFunLike.congr_fun h y)
  let T := fixedPoints Q X ⊕ (Σ i : Fin 10, O i)
  let f : T → X := Sum.elim Subtype.val (fun y => y.2.val)
  have hnot (i : Fin 10) (x : O i) : x.val ∉ fixedPoints Q X := by
    intro hx
    have hcard : Nat.card (orbit Q x.val) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hx
    have he : (Quotient.mk'' x.val : orbitRel.Quotient Q X) = (a i).val :=
      orbitRel.Quotient.mem_orbit.mp ((hxi i) ▸ x.property)
    rw [← orbitRel.Quotient.orbit_mk,he,(a i).property] at hcard
    omega
  have hf : Function.Injective f := by
    intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Subtype.ext huv)
      | inr v =>
        change u.val = v.2.val at huv
        exact False.elim (hnot v.1 v.2 (huv ▸ u.property))
    | inr u =>
      cases v with
      | inl v =>
        change u.2.val = v.val at huv
        exact False.elim (hnot u.1 u.2 (huv.symm ▸ v.property))
      | inr v =>
        have hu : (Quotient.mk'' u.2.val : orbitRel.Quotient Q X) = (a u.1).val :=
          orbitRel.Quotient.mem_orbit.mp ((hxi u.1) ▸ u.2.property)
        have hv : (Quotient.mk'' v.2.val : orbitRel.Quotient Q X) = (a v.1).val :=
          orbitRel.Quotient.mem_orbit.mp ((hxi v.1) ▸ v.2.property)
        have hij : u.1 = v.1 := a.injective (Subtype.ext
          (hu.symm.trans ((congrArg Quotient.mk'' huv).trans hv)))
        rcases u with ⟨i,u⟩
        rcases v with ⟨j,v⟩
        dsimp only at hij
        subst j
        have huv' : u = v := Subtype.ext huv
        subst v
        rfl
  have hT : Nat.card T = 36 := by
    change Nat.card (fixedPoints Q X ⊕ (Σ i : Fin 10, O i)) = 36
    rw [Nat.card_sum,Nat.card_sigma,hF]
    simp only [hO,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  let s := (Set.range f).toFinite.toFinset
  refine ⟨R,hindex,s,?_,?_⟩
  · rw [← Set.ncard_coe_finset,Set.Finite.coe_toFinset,Set.ncard_range_of_injective hf]
    exact hT
  · intro r x hx
    have hx' : x ∈ Set.range f := by simpa only [s,Set.Finite.mem_toFinset] using hx
    obtain ⟨y,rfl⟩ := hx'
    cases y with
    | inl y => exact y.property r.val
    | inr y => exact hRfixO r y.1 y.2

end FiveTransitive.Degree69ThreeBoundKernel

end CFSG

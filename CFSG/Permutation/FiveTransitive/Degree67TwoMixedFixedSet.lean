module

public import CFSG.Permutation.FiveTransitive.Degree67TwoMixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoMixedFixedSet
open MulAction NormalizerOrbitFamily Degree67TwoMixedAction

theorem exists_fixed_set
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (hF : Nat.card (fixedPoints Q X) = 5)
    (p : Family (X := X) Q 2) (a : Fin 4 ↪ Family (X := X) Q 4) :
    ∃ s : Finset X, s.card = 23 ∧
      ∀ r : (mixedHom Q p a).ker, ∀ x ∈ s, r • x = x := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let chosen : Option (Fin 4) → orbitRel.Quotient Q X :=
    fun i => i.elim p.val (fun j => (a j).val)
  let O (i : Option (Fin 4)) := orbitAction Q (chosen i)
  have hchosen : Function.Injective chosen := by
    intro u v huv
    cases u with
    | none =>
      cases v with
      | none => rfl
      | some j =>
        have hc := congrArg (fun t : orbitRel.Quotient Q X => Nat.card t.orbit) huv
        change Nat.card p.val.orbit = Nat.card (a j).val.orbit at hc
        rw [p.property,(a j).property] at hc
        omega
    | some i =>
      cases v with
      | none =>
        have hc := congrArg (fun t : orbitRel.Quotient Q X => Nat.card t.orbit) huv
        change Nat.card (a i).val.orbit = Nat.card p.val.orbit at hc
        rw [(a i).property,p.property] at hc
        omega
      | some j => exact congrArg some (a.injective (Subtype.ext huv))
  have hselected (i : Option (Fin 4)) : Nat.card (chosen i).orbit ≠ 1 := by
    cases i with
    | none => change Nat.card p.val.orbit ≠ 1; rw [p.property]; decide
    | some i => change Nat.card (a i).val.orbit ≠ 1; rw [(a i).property]; decide
  have hRfix (r : (mixedHom Q p a).ker) (i : Option (Fin 4)) (y : O i) :
      r • y.val = y.val := by
    cases i with
    | none =>
      have h := congrArg Prod.fst (show mixedHom Q p a r.val = 1 from r.property)
      exact congrArg Subtype.val (DFunLike.congr_fun h y)
    | some i =>
      have h := congrFun (congrArg Prod.snd (show mixedHom Q p a r.val = 1 from r.property)) i
      exact congrArg Subtype.val (DFunLike.congr_fun h y)
  let T := fixedPoints Q X ⊕ (Σ i : Option (Fin 4), O i)
  let f : T → X := Sum.elim Subtype.val (fun y => y.2.val)
  have hnot (i : Option (Fin 4)) (x : O i) : x.val ∉ fixedPoints Q X := by
    intro hx
    have hcard : Nat.card (orbit Q x.val) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hx
    have he : (Quotient.mk'' x.val : orbitRel.Quotient Q X) = chosen i :=
      orbitRel.Quotient.mem_orbit.mp x.property
    rw [← orbitRel.Quotient.orbit_mk,he] at hcard
    exact hselected i hcard
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
        have hu : (Quotient.mk'' u.2.val : orbitRel.Quotient Q X) = chosen u.1 :=
          orbitRel.Quotient.mem_orbit.mp u.2.property
        have hv : (Quotient.mk'' v.2.val : orbitRel.Quotient Q X) = chosen v.1 :=
          orbitRel.Quotient.mem_orbit.mp v.2.property
        have hij : u.1 = v.1 := hchosen
          (hu.symm.trans ((congrArg Quotient.mk'' huv).trans hv))
        rcases u with ⟨i,u⟩
        rcases v with ⟨j,v⟩
        dsimp only at hij
        subst j
        have huv' : u = v := Subtype.ext huv
        subst v
        rfl
  have hT : Nat.card T = 23 := by
    change Nat.card (fixedPoints Q X ⊕ (Σ i : Option (Fin 4), O i)) = 23
    have hp : Nat.card (O none) = 2 := p.property
    have ha (i : Fin 4) : Nat.card (O (some i)) = 4 := (a i).property
    rw [Nat.card_sum,Nat.card_sigma,hF,Fintype.sum_option]
    simp only [hp,ha,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    norm_num
  let s := (Set.range f).toFinite.toFinset
  refine ⟨s,?_,?_⟩
  · rw [← Set.ncard_coe_finset,Set.Finite.coe_toFinset,Set.ncard_range_of_injective hf]
    exact hT
  · intro r x hx
    have hx' : x ∈ Set.range f := by simpa only [s,Set.Finite.mem_toFinset] using hx
    obtain ⟨y,rfl⟩ := hx'
    cases y with
    | inl y => exact y.property r.val
    | inr y => exact hRfix r y.1 y.2

end FiveTransitive.Degree67TwoMixedFixedSet

end CFSG

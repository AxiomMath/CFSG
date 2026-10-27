module

public import CFSG.Permutation.FiveTransitive.Degree24SylowFixedAction
public import CFSG.Permutation.FiveTransitive.Degree25FiveCodePermutation

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup
open FiveTransitive.Degree24

private theorem fixingSubgroup_card_support_eq_restriction
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (s : Set X) [DecidablePred (· ∈ s)]
    [Fintype (SubMulAction.ofFixingSubgroup P s)]
    (u : fixingSubgroup P s) :
    ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card) =
      ((MulAction.toPermHom
        (fixingSubgroup P s)
        (SubMulAction.ofFixingSubgroup P s)) u).support.card := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  let g : Equiv.Perm X := ((u : H) : P)
  let r : Equiv.Perm Y :=
    MulAction.toPermHom H Y u
  let val : Y ↪ X :=
    Function.Embedding.subtype _
  have hsupport :
      Finset.map val r.support = g.support := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      apply Equiv.Perm.mem_support.mp hy
      apply Subtype.ext
      change g y.1 = y.1
      exact hfix
    · intro hx
      have hxNotMem : x ∉ s := by
        intro hxs
        exact
          Equiv.Perm.mem_support.mp hx
            ((mem_fixingSubgroup_iff P).mp u.prop x hxs)
      let y : Y := ⟨x, hxNotMem⟩
      have hy : y ∈ r.support := by
        apply Equiv.Perm.mem_support.mpr
        intro hfix
        apply Equiv.Perm.mem_support.mp hx
        exact congrArg Subtype.val hfix
      exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
  calc
    g.support.card =
        (Finset.map val r.support).card := by rw [hsupport]
    _ = r.support.card := Finset.card_map val

theorem exists_fourFive_model_of_sylowImage_card_one_hundred_twenty_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 125) :
    let H : Subgroup P := fixingSubgroup P s
    let Y := SubMulAction.ofFixingSubgroup P s
    let R : Subgroup P :=
      Degree24.sylowImage X P s S
    let eSR : S ≃* R :=
      (S : Subgroup H).equivMapOfInjective
        H.subtype H.subtype_injective
    ∃ A : Subgroup Degree20.FourFiveBase,
      ∃ eAR : A ≃* R,
        ∃ d : Y ≃ Degree20.TwentyFivePoints,
          Nat.card A = 125 ∧
          (∀ a : A,
            ((((eAR a : R) : P) :
                Equiv.Perm X).support.card) =
              5 * fiveWeight
                ((a : A) : Degree20.FourFiveBase)) ∧
          ∀ (a : A) (y : Y),
            d ((MulAction.toPermHom H Y)
                ((eSR.symm (eAR a) : S) : H) y) =
              (MulAction.toPermHom
                Degree20.FourFiveBase
                Degree20.TwentyFivePoints)
                  ((a : A) :
                    Degree20.FourFiveBase) (d y) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let Y := SubMulAction.ofFixingSubgroup P s
  letI : Fintype Y := Fintype.ofFinite Y
  let τ : S →* Equiv.Perm Y :=
    (MulAction.toPermHom H Y).comp
      (S : Subgroup H).subtype
  have hYcard : Fintype.card Y = 20 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card ↥(sᶜ : Set X) = 20
    rw [Nat.card_coe_set_eq]
    have htotal := Set.ncard_add_ncard_compl s
    rw [Nat.card_eq_fintype_card, hcard, hs] at htotal
    omega
  have hHfaithful :
      Function.Injective (MulAction.toPermHom H Y) := by
    intro a b hab
    apply Subtype.ext
    apply P.subtype_injective
    ext x
    by_cases hx : x ∈ s
    · have ha :=
        (mem_fixingSubgroup_iff P).mp a.prop x hx
      have hb :=
        (mem_fixingSubgroup_iff P).mp b.prop x hx
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using
        ha.trans hb.symm
    · let y : Y := ⟨x, hx⟩
      have hy :=
        congrArg (fun q : Equiv.Perm Y => q y) hab
      have hy' := congrArg Subtype.val hy
      simpa [y, Subgroup.smul_def, Equiv.Perm.smul_def] using
        hy'
  have hτinjective : Function.Injective τ :=
    hHfaithful.comp (S : Subgroup H).subtype_injective
  let RY : Subgroup (Equiv.Perm Y) := τ.range
  let eSY : S ≃* RY :=
    MonoidHom.ofInjective hτinjective
  have hRYcard : Nat.card RY = 125 := by
    calc
      Nat.card RY = Nat.card S :=
        Nat.card_congr eSY.symm.toEquiv
      _ = 125 := hScard
  obtain ⟨A, eAY, d, hAcard, hsupportY,
      hequivariantY⟩ :=
    exists_fourFive_model_of_subgroup_card_one_hundred_twenty_five
      Y hYcard RY hRYcard
  let R : Subgroup P :=
    Degree24.sylowImage X P s S
  let eSR : S ≃* R :=
    (S : Subgroup H).equivMapOfInjective
      H.subtype H.subtype_injective
  let eAR : A ≃* R :=
    eAY.trans (eSY.symm.trans eSR)
  refine ⟨A, eAR, d, hAcard, ?_, ?_⟩
  · intro a
    let q : S := eSY.symm (eAY a)
    have hrestrict :
        ((eAY a : RY) : Equiv.Perm Y) =
          τ q := by
      exact
        (MonoidHom.apply_ofInjective_symm
          hτinjective (eAY a)).symm
    have heSR :
        ((eSR q : R) : P) = (q : H) := by
      exact
        Subgroup.coe_equivMapOfInjective_apply
          (S : Subgroup H) H.subtype
            H.subtype_injective q
    calc
      ((((eAR a : R) : P) :
            Equiv.Perm X).support.card) =
          ((MulAction.toPermHom H Y) (q : H)).support.card := by
        change
          ((((eSR q : R) : P) :
              Equiv.Perm X).support.card) =
            ((MulAction.toPermHom H Y) (q : H)).support.card
        rw [heSR]
        exact
          fixingSubgroup_card_support_eq_restriction
            X P s (q : H)
      _ = ((eAY a : RY) :
            Equiv.Perm Y).support.card := by
        rw [hrestrict]
        rfl
      _ = 5 * fiveWeight
            ((a : A) : Degree20.FourFiveBase) :=
        hsupportY a
  · intro a y
    have heSRsymm :
        eSR.symm (eAR a) =
          eSY.symm (eAY a) := by
      apply eSR.injective
      simp only [eAR, MulEquiv.trans_apply,
        eSR.apply_symm_apply]
    rw [heSRsymm]
    change
      d ((τ (eSY.symm (eAY a))) y) =
        (MulAction.toPermHom
          Degree20.FourFiveBase
          Degree20.TwentyFivePoints)
            ((a : A) :
              Degree20.FourFiveBase) (d y)
    rw [MonoidHom.apply_ofInjective_symm
      hτinjective]
    exact hequivariantY a y

end FiveTransitive.Degree25

end CFSG

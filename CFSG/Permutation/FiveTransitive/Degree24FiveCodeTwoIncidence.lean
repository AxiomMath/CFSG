module

public import CFSG.Permutation.FiveTransitive.Degree24FiveCodeTwoPermutation

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem sylow_five_card_twenty_five_fixedPoints_eq_nine
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (T : Sylow 5 (fixingSubgroup P s))
    (hTcard : Nat.card T = 25) :
    Nat.card (MulAction.fixedPoints T X) = 9 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let inclusion : T →* Equiv.Perm X :=
    P.subtype.comp
      (H.subtype.comp
        (T : Subgroup H).subtype)
  have hinclusion : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  let R : Subgroup (Equiv.Perm X) :=
    inclusion.range
  let eTR : T ≃* R :=
    MonoidHom.ofInjective hinclusion
  have hRcard : Nat.card R = 25 := by
    calc
      Nat.card R = Nat.card T :=
        Nat.card_congr eTR.symm.toEquiv
      _ = 25 := hTcard
  have hsFixed :
      s ⊆ MulAction.fixedPoints R X := by
    intro x hx
    rw [MulAction.mem_fixedPoints]
    intro r
    obtain ⟨u, hu⟩ := r.prop
    change (r.1 : Equiv.Perm X) x = x
    rw [← hu]
    have hfix :=
      (mem_fixingSubgroup_iff P).mp
        (((T : Subgroup H).subtype u : H).prop)
        x hx
    change
      (((u : H) : P) : Equiv.Perm X) x = x
    simpa [Subgroup.smul_def,
      Equiv.Perm.smul_def] using hfix
  rcases
      subgroup_card_twenty_five_support_distribution
        X hcard R hRcard with
    hfive | ⟨hfixedNine, _, _⟩ |
      ⟨hfixedFour, _⟩
  · obtain ⟨r⟩ :=
      (Nat.card_pos_iff.mp hfive).1
    have hr :
        (r.1.1 : Equiv.Perm X).support.card = 5 :=
      r.prop
    obtain ⟨u, hu⟩ := r.1.prop
    have hmem :
        (r.1 : Equiv.Perm X) ∈ P := by
      rw [← hu]
      exact
        (((T : Subgroup H).subtype u : H) : P).prop
    have hne : (r.1 : Equiv.Perm X) ≠ 1 := by
      intro hrone
      rw [hrone, Equiv.Perm.support_one] at hr
      norm_num at hr
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5 hmem hne (by omega)))
  · let Efixed :
      MulAction.fixedPoints R X ≃
          MulAction.fixedPoints T X := {
      toFun := fun x => ⟨x.1, by
        have hxp := x.prop
        rw [MulAction.mem_fixedPoints] at hxp ⊢
        intro u
        have hx := hxp (eTR u)
        change (inclusion u) x.1 = x.1
        exact hx⟩
      invFun := fun x => ⟨x.1, by
        have hxp := x.prop
        rw [MulAction.mem_fixedPoints] at hxp ⊢
        intro r
        have hx := hxp (eTR.symm r)
        change (r.1 : Equiv.Perm X) x.1 = x.1
        change
          (inclusion (eTR.symm r)) x.1 = x.1 at hx
        rw [show inclusion (eTR.symm r) = r.1 by
          exact congrArg Subtype.val
            (eTR.apply_symm_apply r)] at hx
        exact hx⟩
      left_inv := fun x => by
        apply Subtype.ext
        rfl
      right_inv := fun x => by
        apply Subtype.ext
        rfl }
    calc
      Nat.card (MulAction.fixedPoints T X) =
          Nat.card (MulAction.fixedPoints R X) :=
        Nat.card_congr Efixed.symm
      _ = 9 := hfixedNine
  · have hfixedNcard :
        (MulAction.fixedPoints R X).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hfixedFour
    have hle :=
      Set.ncard_le_ncard hsFixed
    rw [hs, hfixedNcard] at hle
    omega

end FiveTransitive.Degree24

end CFSG

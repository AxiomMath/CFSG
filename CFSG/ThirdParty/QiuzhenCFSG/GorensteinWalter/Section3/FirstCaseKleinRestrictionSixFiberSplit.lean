module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The exact two-coset split behind restriction (6).

If `O` has index two in `D` and `s` is the commuting involution selected in
the restriction-(6) argument, then the `y`-inverted elements of `D` split
into the `y`-inverted elements of `O` and the translate by `s` of the
`(s*y)`-inverted elements of `O`.
-/

private def restrictionSix_fiber_split_equiv
    {G : Type u} [Group G] [Finite G]
    (D O : Subgroup G) {y s : G}
    (hOleD : O ≤ D)
    (hOindex : (O.subgroupOf D).index = 2)
    (hOodd : Nat.Coprime 2 (Nat.card O))
    (hy : IsInvolution y) (hs : IsInvolution s)
    (hsD : s ∈ D) (hsy : s * y = y * s) :
    ({x : G // x ∈ invertedElements O y} ⊕
      {x : G // x ∈ invertedElements O (s * y)}) ≃
      {x : G // x ∈ invertedElements D y} := by
  classical
  have hsnotO : s ∉ O := by
    intro hsO
    have hsSq : (⟨s, hsO⟩ : O) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using hs.2
    have hsOne := eq_one_of_sq_eq_one_of_coprime_two hOodd hsSq
    exact hs.1 (congrArg Subtype.val hsOne)
  have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right
    (by simpa [pow_two] using hs.2)
  let A : Type u := {x : G // x ∈ invertedElements O y}
  let B : Type u := {x : G // x ∈ invertedElements O (s * y)}
  let C : Type u := {x : G // x ∈ invertedElements D y}
  have htranslate : ∀ z : B, s * z.1 ∈ invertedElements D y := by
    intro z
    have hzD : s * z.1 ∈ D := D.mul_mem hsD (hOleD z.2.1)
    have hsyInv : s * y * z.1 * (s * y)⁻¹ = z.1⁻¹ := z.2.2
    have hsyInv'0 : y * z.1 * y⁻¹ = s⁻¹ * z.1⁻¹ * s := by
      calc
        y * z.1 * y⁻¹ = (s⁻¹ * s) * (y * z.1 * y⁻¹) * (s⁻¹ * s) := by simp
        _ = s⁻¹ * (s * y * z.1 * (s * y)⁻¹) * s := by
          simp only [mul_inv_rev]
          group
        _ = s⁻¹ * z.1⁻¹ * s := by rw [hsyInv]
    have hsyInv' : y * z.1 * y⁻¹ = s * z.1⁻¹ * s⁻¹ := by
      simpa [hsInv] using hsyInv'0
    have hInv : y * (s * z.1) * y⁻¹ = (s * z.1)⁻¹ := by
      calc
        y * (s * z.1) * y⁻¹ = (y * s * y⁻¹) * (y * z.1 * y⁻¹) := by group
        _ = s * (s * z.1⁻¹ * s⁻¹) := by
          have hys : y * s * y⁻¹ = s := by
            calc
              y * s * y⁻¹ = s * y * y⁻¹ := by rw [← hsy]
              _ = s := by simp
          rw [hys, hsyInv']
        _ = z.1⁻¹ * s := by
          calc
            s * (s * z.1⁻¹ * s⁻¹) = s * (s * (z.1⁻¹ * s)) := by
              rw [hsInv]
              group
            _ = (s * s) * (z.1⁻¹ * s) := by group
            _ = z.1⁻¹ * s := by
              have hs2 : s * s = 1 := by simpa [pow_two] using hs.2
              rw [hs2]
              simp
        _ = (s * z.1)⁻¹ := by rw [mul_inv_rev, hsInv]
    exact ⟨hzD, hInv⟩
  let f : A ⊕ B → C := Sum.elim
    (fun x => ⟨x.1, ⟨hOleD x.2.1, x.2.2⟩⟩)
    (fun z => ⟨s * z.1, htranslate z⟩)
  have hf_inj : Function.Injective f := by
    intro a b hab
    cases a with
    | inl x =>
        cases b with
        | inl z =>
            have hval : (x : G) = (z : G) :=
              congrArg (fun q : C => (q : G)) hab
            exact congrArg Sum.inl (Subtype.ext hval)
        | inr z =>
            have hval : (x : G) = s * z.1 :=
              congrArg (fun q : C => (q : G)) hab
            have hsO : s ∈ O := by
              have hxsO : x.1 ∈ O := x.2.1
              have hzsO : z.1 ∈ O := z.2.1
              have hsEq : s = x.1 * z.1⁻¹ := by rw [hval]; group
              rw [hsEq]
              exact O.mul_mem hxsO (O.inv_mem hzsO)
            exact (hsnotO hsO).elim
    | inr x =>
        cases b with
        | inl z =>
            have hval : s * x.1 = (z : G) :=
              congrArg (fun q : C => (q : G)) hab
            have hsO : s ∈ O := by
              have hxsO : x.1 ∈ O := x.2.1
              have hzsO : z.1 ∈ O := z.2.1
              have hsEq : s = z.1 * x.1⁻¹ := by rw [← hval]; group
              rw [hsEq]
              exact O.mul_mem hzsO (O.inv_mem hxsO)
            exact (hsnotO hsO).elim
        | inr z =>
            have hval : s * x.1 = s * z.1 :=
              congrArg (fun q : C => (q : G)) hab
            exact congrArg Sum.inr (Subtype.ext (mul_left_cancel hval))
  have hf_surj : Function.Surjective f := by
    intro x
    by_cases hxO : x.1 ∈ O
    · exact ⟨Sum.inl ⟨x.1, ⟨hxO, x.2.2⟩⟩, by rfl⟩
    · have hmulO : s * x.1 ∈ O := by
        have hiff := Subgroup.mul_mem_iff_of_index_two hOindex
          (a := (⟨s, hsD⟩ : D)) (b := (⟨x.1, x.2.1⟩ : D))
        have haO : ¬ (⟨s, hsD⟩ : D) ∈ O.subgroupOf D := by
          intro ha
          exact hsnotO (Subgroup.mem_subgroupOf.mp ha)
        have hbO : ¬ (⟨x.1, x.2.1⟩ : D) ∈ O.subgroupOf D := by
          intro hb
          exact hxO (Subgroup.mem_subgroupOf.mp hb)
        have hmem : (⟨s, hsD⟩ : D) * (⟨x.1, x.2.1⟩ : D) ∈
            O.subgroupOf D :=
          hiff.mpr ⟨fun ha => (haO ha).elim, fun hb => (hbO hb).elim⟩
        simpa using Subgroup.mem_subgroupOf.mp hmem
      have hzInv : (s * y) * (s * x.1) * (s * y)⁻¹ = (s * x.1)⁻¹ := by
        have hs2 : s * s = 1 := by simpa [pow_two] using hs.2
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        have hsys : s * y * s = y := by
          calc
            s * y * s = y * s * s := by rw [hsy]
            _ = y := by simp [hs2, mul_assoc]
        calc
          (s * y) * (s * x.1) * (s * y)⁻¹ =
              y * x.1 * y⁻¹ * s⁻¹ := by
                rw [mul_inv_rev]
                calc
                  s * y * (s * x.1) * (y⁻¹ * s⁻¹) =
                      (s * y * s) * x.1 * y⁻¹ * s⁻¹ := by group
                  _ = y * x.1 * y⁻¹ * s⁻¹ := by rw [hsys]
          _ = x.1⁻¹ * s⁻¹ := by rw [x.2.2]
          _ = (s * x.1)⁻¹ := by rw [mul_inv_rev]
      exact ⟨Sum.inr ⟨s * x.1, ⟨hmulO, hzInv⟩⟩, by
        apply Subtype.ext
        change s * (s * x.1) = x.1
        calc
          s * (s * x.1) = (s * s) * x.1 := by group
          _ = x.1 := by
            have hs2 : s * s = 1 := by simpa [pow_two] using hs.2
            rw [hs2]
            simp⟩
  exact Equiv.ofBijective f ⟨hf_inj, hf_surj⟩

public theorem firstCase_klein_restrictionSix_fiber_card_split
    {G : Type u} [Group G] [Finite G]
    (D O : Subgroup G) {y s : G}
    (hOleD : O ≤ D)
    (hOindex : (O.subgroupOf D).index = 2)
    (hOodd : Nat.Coprime 2 (Nat.card O))
    (hy : IsInvolution y) (hs : IsInvolution s)
    (hsD : s ∈ D) (hsy : s * y = y * s) :
    Nat.card {x : G // x ∈ invertedElements D y} =
      Nat.card {x : G // x ∈ invertedElements O y} +
        Nat.card {x : G // x ∈ invertedElements O (s * y)} := by
  classical
  let e := restrictionSix_fiber_split_equiv D O hOleD hOindex hOodd
    hy hs hsD hsy
  calc
    Nat.card {x : G // x ∈ invertedElements D y} =
        Nat.card ({x : G // x ∈ invertedElements O y} ⊕
          {x : G // x ∈ invertedElements O (s * y)}) :=
          Nat.card_congr e.symm
    _ = Nat.card {x : G // x ∈ invertedElements O y} +
          Nat.card {x : G // x ∈ invertedElements O (s * y)} :=
          Nat.card_sum

/-- Element-wise version of the restriction-(6) fiber split: every
`y`-inverted element of `D` lies in `O`, or is `s * z` for a
`(s*y)`-inverted element `z` of `O`. -/
public theorem firstCase_klein_restrictionSix_fiber_mem_split
    {G : Type u} [Group G] [Finite G]
    (D O : Subgroup G) {y s : G}
    (hOleD : O ≤ D)
    (hOindex : (O.subgroupOf D).index = 2)
    (hOodd : Nat.Coprime 2 (Nat.card O))
    (hy : IsInvolution y) (hs : IsInvolution s)
    (hsD : s ∈ D) (hsy : s * y = y * s) :
    ∀ x : G, x ∈ invertedElements D y →
      x ∈ invertedElements O y ∨
        ∃ z : G, z ∈ invertedElements O (s * y) ∧ x = s * z := by
  classical
  let e := restrictionSix_fiber_split_equiv D O hOleD hOindex hOodd
    hy hs hsD hsy
  intro x hx
  rcases hSymm : e.symm ⟨x, hx⟩ with a | b
  · have hEq : (a : G) = x := by
      have hImg : e (Sum.inl a) = ⟨x, hx⟩ := by
        rw [← hSymm]
        exact e.right_inv ⟨x, hx⟩
      exact congrArg Subtype.val hImg
    rw [← hEq]
    exact Or.inl a.2
  · have hEq : (s * (b : G)) = x := by
      have hImg : e (Sum.inr b) = ⟨x, hx⟩ := by
        rw [← hSymm]
        exact e.right_inv ⟨x, hx⟩
      exact congrArg Subtype.val hImg
    rw [← hEq]
    exact Or.inr ⟨b.1, b.2, rfl⟩

end CFSG.GorensteinWalter

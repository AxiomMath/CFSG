module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenOuterRegion
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transport of conjugate families

Conjugating the ambient product region gives a bijection between the
conjugates of `P` in `P ⊔ E` and the conjugates of `P^g` in
`(P ⊔ E)^g`.  The cardinality statement is used for the total fibre count in
the transported equation-(11) regions.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private lemma conj_conj_cf
    {G : Type u} [Group G] {H : Subgroup G} (a b : G) :
    conjugateSubgroup (conjugateSubgroup H a) b =
      conjugateSubgroup H (b * a) := by
  change (H.map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj b).toMonoidHom =
    H.map (MulAut.conj (b * a)).toMonoidHom
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private lemma conj_sup_cf
    {G : Type u} [Group G] (H K : Subgroup G) (g : G) :
    conjugateSubgroup (H ⊔ K) g =
      conjugateSubgroup H g ⊔ conjugateSubgroup K g := by
  change (H ⊔ K).map (MulAut.conj g).toMonoidHom =
    H.map (MulAut.conj g).toMonoidHom ⊔
      K.map (MulAut.conj g).toMonoidHom
  exact Subgroup.map_sup H K (MulAut.conj g).toMonoidHom

private lemma conj_one_cf
    {G : Type u} [Group G] {H : Subgroup G} :
    conjugateSubgroup H (1 : G) = H := by
  change H.map (MulAut.conj (1 : G)).toMonoidHom = H
  rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
    ext x; simp, Subgroup.map_id]

private def subgroup_conj_equiv
    {G : Type u} [Group G] (g : G) : Subgroup G ≃ Subgroup G :=
  { toFun := fun H => conjugateSubgroup H g
    invFun := fun H => conjugateSubgroup H g⁻¹
    left_inv := by
      intro H
      change conjugateSubgroup (conjugateSubgroup H g) g⁻¹ = H
      rw [conj_conj_cf, inv_mul_cancel, conj_one_cf]
    right_inv := by
      intro H
      change conjugateSubgroup (conjugateSubgroup H g⁻¹) g = H
      rw [conj_conj_cf, mul_inv_cancel, conj_one_cf] }

/-- Conjugation preserves the cardinality of the product-region conjugate
family. -/
public theorem secondCase_linear_conjugate_family_card_transport
    {G : Type u} [Group G] [Finite G]
    (P E : Subgroup G) (a : G) :
    Nat.card {Y : Subgroup G //
      Y ≤ P ⊔ E ∧ Y ≠ P ∧
        (∃ h : G, Y = conjugateSubgroup P h)} =
      Nat.card {Y : Subgroup G //
      Y ≤ conjugateSubgroup (P ⊔ E) a ∧
        Y ≠ conjugateSubgroup P a ∧
        (∃ h : G, Y = conjugateSubgroup P h)} := by
  classical
  let e := subgroup_conj_equiv a
  let f : {Y : Subgroup G //
      Y ≤ P ⊔ E ∧ Y ≠ P ∧
        (∃ h : G, Y = conjugateSubgroup P h)} ≃
      {Y : Subgroup G //
      Y ≤ conjugateSubgroup (P ⊔ E) a ∧
        Y ≠ conjugateSubgroup P a ∧
        (∃ h : G, Y = conjugateSubgroup P h)} :=
    { toFun := fun Y =>
        ⟨e Y.1, by
          change conjugateSubgroup Y.1 a ≤ conjugateSubgroup (P ⊔ E) a
          exact Subgroup.map_mono Y.2.1
        , by
          intro heq
          apply Y.2.2.1
          have := congrArg (fun H : Subgroup G => conjugateSubgroup H a⁻¹) heq
          simpa [e, subgroup_conj_equiv, conj_conj_cf, conj_one_cf,
            mul_assoc] using this
        , by
          rcases Y.2.2.2 with ⟨h, hh⟩
          refine ⟨a * h, ?_⟩
          rw [hh]
          simp [e, subgroup_conj_equiv, conj_conj_cf, mul_assoc]⟩
      invFun := fun Y =>
        ⟨e.symm Y.1, by
          have hmap : conjugateSubgroup Y.1 a⁻¹ ≤
              conjugateSubgroup (conjugateSubgroup (P ⊔ E) a) a⁻¹ :=
            Subgroup.map_mono Y.2.1
          simpa [e, subgroup_conj_equiv, conj_conj_cf, conj_one_cf,
            mul_assoc] using hmap
        , by
          intro heq
          apply Y.2.2.1
          have := congrArg (fun H : Subgroup G => conjugateSubgroup H a) heq
          simpa [e, subgroup_conj_equiv, conj_conj_cf, conj_one_cf,
            mul_assoc] using this
        , by
          rcases Y.2.2.2 with ⟨h, hh⟩
          refine ⟨a⁻¹ * h, ?_⟩
          rw [hh]
          simp [e, subgroup_conj_equiv, conj_conj_cf, mul_assoc]⟩
      left_inv := by
        intro Y
        apply Subtype.ext
        exact e.left_inv Y.1
      right_inv := by
        intro Y
        apply Subtype.ext
        exact e.right_inv Y.1 }
  exact Nat.card_congr f

end CFSG.GorensteinWalter

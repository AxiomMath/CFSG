module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.GroupTheory

variable {G H : Type*} [Group G] [Group H]

noncomputable def normalizerRangeEquivMap (E : Subgroup G) (e : G ≃* H) :
    E.normalizerMonoidHom.range ≃* (E.map e.toMonoidHom).normalizerMonoidHom.range := by
  let ψ : E ≃* E.map (e : G →* H) := e.subgroupMap E
  let ρ : MulAut E ≃* MulAut (E.map (e : G →* H)) := MulAut.congr ψ
  let η : Subgroup.normalizer (E : Set G) ≃*
      Subgroup.normalizer ((E.map (e : G →* H)) : Set H) :=
    (e.subgroupMap (Subgroup.normalizer (E : Set G))).trans
      (MulEquiv.subgroupCongr (Subgroup.map_equiv_normalizer_eq E e))
  have hη : ∀ n : Subgroup.normalizer (E : Set G), (η n : H) = e (n : G) := by
    intro n
    rfl
  have hcomp : ρ.toMonoidHom.comp E.normalizerMonoidHom =
      (E.map (e : G →* H)).normalizerMonoidHom.comp η.toMonoidHom := by
    refine MonoidHom.ext fun n => ?_
    refine MulEquiv.ext fun x => ?_
    obtain ⟨u, rfl⟩ := ψ.surjective x
    change (MulAut.congr ψ (E.normalizerMonoidHom n)) (ψ u) =
      ((E.map (e : G →* H)).normalizerMonoidHom (η n)) (ψ u)
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    apply Subtype.ext
    change e ((E.normalizerMonoidHom n) u : G) =
      (η n : H) * e (u : G) * (η n : H)⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hη]
    simp
  have hrange : E.normalizerMonoidHom.range.map ρ.toMonoidHom =
      (E.map (e : G →* H)).normalizerMonoidHom.range := by
    rw [MonoidHom.map_range, hcomp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr η.surjective, Subgroup.map_top]
  change E.normalizerMonoidHom.range ≃*
    (E.map (e : G →* H)).normalizerMonoidHom.range
  exact (ρ.subgroupMap E.normalizerMonoidHom.range).trans (MulEquiv.subgroupCongr hrange)

theorem isPerfect_normalizerRange_iff (E : Subgroup G) (e : G ≃* H) :
    Group.IsPerfect E.normalizerMonoidHom.range ↔
      Group.IsPerfect (E.map e.toMonoidHom).normalizerMonoidHom.range := by
  constructor
  · intro h
    exact Group.IsPerfect.ofSurjective
      (f := (normalizerRangeEquivMap E e).toMonoidHom) (normalizerRangeEquivMap E e).surjective
  · intro h
    exact Group.IsPerfect.ofSurjective
      (f := (normalizerRangeEquivMap E e).symm.toMonoidHom)
      (normalizerRangeEquivMap E e).symm.surjective

end CFSG.GroupTheory

end

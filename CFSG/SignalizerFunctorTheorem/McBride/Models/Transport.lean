module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Defs
import CFSG.GroupTheory.Fitting.MulEquiv

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {X Y : Type*} [Group X] [Group Y]

theorem signalizerFixedSubgroup_congr (e : X ≃* Y) (f : MulAut X) :
    signalizerFixedSubgroup (MulAut.congr e f) = (signalizerFixedSubgroup f).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change e (f (e.symm y)) = y ↔ f (e.symm y) = e.symm y
  exact e.eq_symm_apply.symm

theorem orderOf_congr (e : X ≃* Y) (f : MulAut X) : orderOf (MulAut.congr e f) = orderOf f :=
  orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective f

theorem congr_symm_congr (e : X ≃* Y) (f : MulAut X) :
    MulAut.congr e.symm (MulAut.congr e f) = f := by
  ext x
  simp

theorem fittingSubgroup_map_equiv (e : X ≃* Y) :
    (CFSG.fittingSubgroup X).map e.toMonoidHom = CFSG.fittingSubgroup Y :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv e

theorem fittingSubgroupOf_map_equiv (e : X ≃* Y) (H : Subgroup X) :
    CFSG.fittingSubgroupOf (H.map e.toMonoidHom) =
      (CFSG.fittingSubgroupOf H).map e.toMonoidHom := by
  have h1 := fittingSubgroup_map_equiv (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective)
  have h2 : (H.map e.toMonoidHom).subtype.comp
      (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toMonoidHom =
      e.toMonoidHom.comp H.subtype := by
    ext x
    rfl
  unfold CFSG.fittingSubgroupOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem centralizer_map_equiv (e : X ≃* Y) (H : Subgroup X) :
    Subgroup.centralizer ((H.map e.toMonoidHom : Subgroup Y) : Set Y) =
      (Subgroup.centralizer (H : Set X)).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have := h (e x) (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    apply e.injective
    simpa using this
  · intro h z hz
    have hz' : e.symm z ∈ H := by simpa using Subgroup.mem_map_equiv.mp hz
    have := h (e.symm z) hz'
    apply e.symm.injective
    simpa using this

theorem isPGroup_of_map_equiv {p : ℕ} (e : X ≃* Y) {H : Subgroup X}
    (h : IsPGroup p (H.map e.toMonoidHom)) : IsPGroup p H :=
  h.of_equiv (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).symm

theorem isSolvable_of_map_equiv (e : X ≃* Y) {H : Subgroup X}
    (h : Group.IsSolvable (H.map e.toMonoidHom)) : Group.IsSolvable H :=
  Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).injective

theorem isMulCommutative_of_map_equiv (e : X ≃* Y) {H : Subgroup X}
    (h : IsMulCommutative (H.map e.toMonoidHom)) : IsMulCommutative H := by
  have := Subgroup.comap_injective_isMulCommutative (H := H.map e.toMonoidHom)
    (f := e.toMonoidHom) e.injective
  rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at this

theorem normal_subgroupOf_map_equiv (e : X ≃* Y) {N C : Subgroup X} (hNC : N ≤ C)
    (h : (N.subgroupOf C).Normal) :
    ((N.map e.toMonoidHom).subgroupOf (C.map e.toMonoidHom)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hNC)]
  rw [Subgroup.normal_subgroupOf_iff hNC] at h
  intro a k ha hk
  rw [Subgroup.mem_map_equiv] at ha hk ⊢
  have := h (e.symm a) (e.symm k) ha hk
  simpa using this

theorem fixedFitting_congr (e : X ≃* Y) (f : MulAut X) :
    fixedFitting (MulAut.congr e f) = (fixedFitting f).map e.toMonoidHom := by
  unfold fixedFitting
  rw [signalizerFixedSubgroup_congr, fittingSubgroupOf_map_equiv]

theorem fixedNormalizer_congr (e : X ≃* Y) (f : MulAut X) :
    fixedNormalizer (MulAut.congr e f) = (fixedNormalizer f).map e.toMonoidHom := by
  unfold fixedNormalizer
  rw [fixedFitting_congr, ← Subgroup.map_equiv_normalizer_eq]

theorem fixedCore1_congr (e : X ≃* Y) (f : MulAut X) :
    fixedCore1 (MulAut.congr e f) = (fixedCore1 f).map e.toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change (y ∈ signalizerFixedSubgroup (MulAut.congr e f) ∧
      ∀ x ∈ signalizerFixedSubgroup (MulAut.congr e f), ⁅y, x⁆ ∈ fixedFitting (MulAut.congr e f)) ↔
    (e.symm y ∈ signalizerFixedSubgroup f ∧
      ∀ x ∈ signalizerFixedSubgroup f, ⁅e.symm y, x⁆ ∈ fixedFitting f)
  rw [signalizerFixedSubgroup_congr, fixedFitting_congr]
  simp only [Subgroup.mem_map_equiv]
  refine and_congr Iff.rfl ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · have := h (e x) (by simpa using hx)
    simpa using this
  · have := h (e.symm x) (by simpa using hx)
    simpa using this

theorem fixedFitting_eq_of_fixed_eq {f f' : MulAut X}
    (hC : signalizerFixedSubgroup f = signalizerFixedSubgroup f') :
    fixedFitting f = fixedFitting f' := by
  unfold fixedFitting
  rw [hC]

theorem fixedNormalizer_eq_of_fixed_eq {f f' : MulAut X}
    (hC : signalizerFixedSubgroup f = signalizerFixedSubgroup f') :
    fixedNormalizer f = fixedNormalizer f' := by
  unfold fixedNormalizer
  rw [fixedFitting_eq_of_fixed_eq hC]

theorem fixedCore1_eq_of_fixed_eq {f f' : MulAut X}
    (hC : signalizerFixedSubgroup f = signalizerFixedSubgroup f') :
    fixedCore1 f = fixedCore1 f' := by
  ext c
  change (c ∈ signalizerFixedSubgroup f ∧
      ∀ x ∈ signalizerFixedSubgroup f, ⁅c, x⁆ ∈ fixedFitting f) ↔
    (c ∈ signalizerFixedSubgroup f' ∧
      ∀ x ∈ signalizerFixedSubgroup f', ⁅c, x⁆ ∈ fixedFitting f')
  rw [hC, fixedFitting_eq_of_fixed_eq hC]

end CFSG.SignalizerFunctorTheorem.McBride

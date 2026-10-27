module

public import CFSG.RankThree.PartTwo.Sec18.Item185OuterLin
import CFSG.RankThree.PartTwo.Sec18.Item185FixedFacts
import CFSG.RankThree.PartTwo.Sec18.Item185PGL3
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieField
public import CFSG.RankThree.PartTwo.Sec13.Item13Models

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item185Proof

open CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  (projectiveSL proj proj_surjective proj_eq_one_iff scalars_le_center scalars_eq_center fieldAut)
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
  (linFix linFix_fixed commutator_mem_range_linFix isSimpleGroup_range_linFix)
open CFSG.GH74.GLS.IVK (fixedField)
open scoped commutatorElement

private theorem mem_fixedSubgroup_gapL3 {S : Type} [Group S] (σ : MulAut S) (x : S) :
    x ∈ fixedSubgroup σ ↔ σ x = x := Iff.rfl

private theorem fixedSubgroup_conj_eq {S : Type} [Group S] (g τ : MulAut S) :
    fixedSubgroup (g * τ * g⁻¹) = (fixedSubgroup τ).map (MulEquiv.toMonoidHom g) := by
  ext y
  rw [mem_fixedSubgroup_gapL3, Subgroup.mem_map]
  constructor
  · intro hy
    rw [MulAut.mul_apply, MulAut.mul_apply] at hy
    refine ⟨g⁻¹ y, ?_, ?_⟩
    · rw [mem_fixedSubgroup_gapL3]
      apply MulEquiv.injective g
      rw [hy, MulAut.apply_inv_self _ g]
    · exact MulAut.apply_inv_self _ g y
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixedSubgroup_gapL3] at hx
    rw [MulAut.mul_apply, MulAut.mul_apply]
    show g (τ (g⁻¹ (g x))) = g x
    rw [MulAut.inv_apply_self _ g, hx]

private theorem fixedFactsAt_conj {S : Type} [Group S] (g τ : MulAut S) (h : FixedFactsAt τ) :
    FixedFactsAt (g * τ * g⁻¹) := by
  let e : fixedSubgroup τ ≃* fixedSubgroup (g * τ * g⁻¹) :=
    (Subgroup.equivMapOfInjective (fixedSubgroup τ) (MulEquiv.toMonoidHom g)
        (MulEquiv.injective g)).trans
      (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq g τ).symm)
  rcases h with h | h
  · exact Or.inl (HasNormalSimpleCentralizer.of_mulEquiv e h)
  · exact Or.inr fun hd => h (by rwa [Nat.card_congr e.toEquiv])

private theorem mem_center_of_central_commutators {K : Type} [Field K]
    {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hcent : ∀ {i j : Fin 3} (hij : i ≠ j),
      ⁅g, Matrix.SpecialLinearGroup.transvection hij (1 : K)⁆ ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) :
    g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  have hcomm : ∀ {i j : Fin 3} (hij : i ≠ j),
      Commute g (Matrix.SpecialLinearGroup.transvection hij (1 : K)) := by
    intro i j hij
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
    have hword : ⁅Matrix.SpecialLinearGroup.transvection hki.symm (1 : K),
        Matrix.SpecialLinearGroup.transvection hkj (1 : K)⁆ =
          Matrix.SpecialLinearGroup.transvection hij (1 : K) := by
      simpa only [mul_one] using Matrix.SpecialLinearGroup.commutatorElement_transvection
        hki.symm hkj hij (1 : K) (1 : K)
    have hconj := Sec13.conj_commutator_eq (hcent hki.symm) (hcent hkj)
    rw [← commutatorElement_def, hword] at hconj
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hpair : Pairwise fun i j : Fin 3 =>
      Commute (Matrix.single i j (1 : K)) (g : Matrix (Fin 3) (Fin 3) K) := by
    intro i j hij
    have h3 := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 3) K =>
      (z : Matrix (Fin 3) (Fin 3) K)) (hcomm hij).eq
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.transvection_coe,
      mul_add, add_mul, mul_one, one_mul] at h3
    exact (add_left_cancel h3).symm
  obtain ⟨r, hr⟩ := Matrix.mem_range_scalar_of_commute_single hpair
  rw [Subgroup.mem_center_iff]
  intro B
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hr]
  exact (Matrix.scalar_commute r (fun s => Commute.all r s) _).eq.symm

private theorem eq_one_of_commute_range_linFix {K : Type} [Field K] (φ : K ≃+* K)
    {x : projectiveSL 3 K} (hx : ∀ y ∈ (linFix φ).range, x * y = y * x) : x = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  refine proj_eq_one_iff.mpr ?_
  rw [scalars_eq_center]
  refine mem_center_of_central_commutators fun {i j} hij => ?_
  refine scalars_le_center 3 K (proj_eq_one_iff.mp ?_)
  have h1 : linFix φ (Matrix.SpecialLinearGroup.transvection hij (1 : fixedField φ)) =
      proj 3 K (Matrix.SpecialLinearGroup.transvection hij (1 : K)) := by
    rw [linFix, MonoidHom.comp_apply, Matrix.SpecialLinearGroup.map_transvection]
    rfl
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, ← h1]
  exact hx _ (MonoidHom.mem_range.mpr ⟨_, rfl⟩)

private theorem fixedFactsAt_fieldAut {K : Type} [Field K] (φ : K ≃+* K) :
    FixedFactsAt (fieldAut 3 K φ) := by
  haveI hsimple := isSimpleGroup_range_linFix φ
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (fixedField φ)) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le le_rfl
  haveI : Group.IsPerfect (linFix φ).range := Group.IsPerfect.range _
  refine fixedFactsAt_of_normal (P := (linFix φ).range) ?_ ?_ hsimple ?_ ?_
  · rintro _ ⟨g₀, rfl⟩
    exact linFix_fixed φ g₀
  · intro a ha b hb
    exact commutator_mem_range_linFix φ ha hb
  · intro hc
    haveI : Nontrivial ↥(linFix φ).range := hsimple.toNontrivial
    have hcomm : IsMulCommutative ↥(linFix φ).range := ⟨⟨hc⟩⟩
    exact Group.IsPerfect.not_isMulCommutative _ hcomm
  · intro x _ hx
    exact eq_one_of_commute_range_linFix φ hx

theorem gapL3Field_holds : GapL3Field := by
  intro n K _ _ _ _ _ σ hσ3 hσD
  obtain ⟨φ, -, H, rfl⟩ := KFacts.linear_order_three_field_descent (le_refl 3) σ hσ3 hσD
  exact fixedFactsAt_conj _ _ (fixedFactsAt_fieldAut φ)

end CFSG.RankThree.PartTwo.Sec18.Item185Proof

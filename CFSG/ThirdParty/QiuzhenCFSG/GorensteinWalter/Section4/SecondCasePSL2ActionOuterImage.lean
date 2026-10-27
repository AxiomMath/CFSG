module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OuterInvolutionTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2InvolutionInnerImage
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Outer involutions remain outer in the linear model

The semilinear action has odd kernel.  If an involution outside the selected
component had a projective image in the derived `PSL₂` layer, comparison with
a component lift would put its image in the odd kernel.  Passing to `M/E`
then makes its coset simultaneously of odd order and of order dividing two,
which is impossible.  Thus the projective image is genuinely outer.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix

universe u

/-- An involution of `M` outside `E` has an outer `PGL₂` image under the
Section-4 linear action. -/
public theorem secondCase_psl2_action_outer_image
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (r : w.M) (hrI : IsInvolution (r : G))
    (hrE : (r : G) ∉ d.E) :
    ∃ r0 : PGL2 K, ad.f r = SemidirectProduct.inl r0 ∧
      r0 ∉ commutator (PGL2 K) := by
  obtain ⟨r0, hr0⟩ :=
    secondCase_psl2_action_involution_inner w d K ad r hrI
  refine ⟨r0, hr0, ?_⟩
  intro hr0J
  have hcard : 3 < Nat.card K := ad.fieldCardGtThree
  have hr0range : r0 ∈ Matrix.ProjectiveSpecialLinearGroup.toPGL.range := by
    rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K ad.primePower hcard]
    exact hr0J
  rcases MonoidHom.mem_range.mp hr0range with ⟨z, hz⟩
  let q : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  let e := ad.modelEquiv.some
  let ybar : d.E ⧸ Subgroup.center d.E := e.symm z
  obtain ⟨y, hy⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.center d.E) ybar
  let yM : w.M := ⟨(y : G), d.E_component.1 y.2⟩
  have hφy : secondCasePSL2ComponentPGLMap d K ad y = r0 := by
    have hqy : e (q y) = z := by
      rw [hy]
      simp [ybar]
    rw [secondCase_psl2_componentPGLMap_apply]
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (e (q y)) = r0
    rw [hqy]
    exact hz
  have hfy : ad.f yM = SemidirectProduct.inl r0 := by
    calc
      ad.f yM = SemidirectProduct.inl
          (secondCasePSL2ComponentPGLMap d K ad y) := by
            simpa [yM] using
              secondCase_psl2_action_on_component_eq_inl w d K ad y
      _ = SemidirectProduct.inl r0 := by rw [hφy]
  have hfr : ad.f r = ad.f yM := hr0.trans hfy.symm
  let h : w.M := r * yM⁻¹
  have hhker : h ∈ ad.f.ker := by
    rw [MonoidHom.mem_ker]
    dsimp [h]
    rw [map_mul, map_inv, hfr]
    simp
  have hhodd : Odd (orderOf h) := by
    have hdiv : orderOf h ∣ Nat.card ad.f.ker :=
      Subgroup.orderOf_dvd_natCard ad.f.ker hhker
    exact Odd.of_dvd_nat ad.ker_odd hdiv
  let E0 : Subgroup w.M := d.E.subgroupOf w.M
  have hE0normal : E0.Normal := by
    rw [Subgroup.normal_subgroupOf_iff d.E_component.1]
    intro x y hx hy
    exact d.E_normal.2 y hy x hx
  let qM : w.M →* (w.M ⧸ E0) := QuotientGroup.mk' E0
  have hyE0 : yM ∈ E0 := Subgroup.mem_subgroupOf.mpr y.2
  have hq_y : qM yM = 1 :=
    (QuotientGroup.eq_one_iff (N := E0) yM).mpr hyE0
  have hq_h : qM h = qM r := by
    dsimp [h]
    rw [map_mul, map_inv, hq_y]
    simp
  have hr2 : r ^ 2 = 1 := Subtype.ext hrI.2
  have hq_rsq : (qM r) ^ 2 = 1 := by
    rw [← map_pow]
    simpa using congrArg qM hr2
  have hq_hodd : Odd (orderOf (qM h)) := by
    have hdiv : orderOf (qM h) ∣ orderOf h := orderOf_map_dvd qM h
    exact Odd.of_dvd_nat hhodd hdiv
  have hq_hone : qM h = 1 := by
    have hdiv : orderOf (qM h) ∣ 2 := by
      rw [hq_h]
      exact orderOf_dvd_of_pow_eq_one hq_rsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | htwo
    · exact orderOf_eq_one_iff.mp hone
    · rw [htwo] at hq_hodd
      norm_num at hq_hodd
  have hq_rone : qM r = 1 := hq_h ▸ hq_hone
  have hrE0 : r ∈ E0 :=
    (QuotientGroup.eq_one_iff (N := E0) r).mp hq_rone
  exact hrE (Subgroup.mem_subgroupOf.mp hrE0)

end CFSG.GorensteinWalter

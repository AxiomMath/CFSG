module

public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GroupTheory

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem eq_bot_of_isPerfect_of_isSolvable {X : Type*} [Group X] {K : Subgroup X}
    (hP : Group.IsPerfect K) (hS : Group.IsSolvable K) : K = ⊥ := by
  by_contra hne
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  exact Group.IsPerfect.not_isSolvable K hS

theorem le_of_isPerfect_of_le_sup_of_subgroupOf_normal {H : Type*} [Group H]
    {A L N P : Subgroup H} (hAL : A ≤ L) (hAn : (A.subgroupOf L).Normal) [N.Normal]
    (hNsol : Group.IsSolvable N) (hP : Group.IsPerfect P) (hPL : P ≤ L) (hPAN : P ≤ A ⊔ N) :
    P ≤ A := by
  set π := QuotientGroup.mk' (A.subgroupOf L)
  have hsub : (P.subgroupOf L).map π ≤ (N.subgroupOf L).map π := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, n, hn, han⟩ := Subgroup.mem_sup_of_normal_right.mp (hPAN hx)
    have hxa : (x : H) * a⁻¹ ∈ N := by
      have han' : a * n = (x : H) := han
      rw [← han']
      exact Subgroup.Normal.conj_mem inferInstance n hn a
    refine ⟨⟨x * a⁻¹, L.mul_mem x.2 (L.inv_mem (hAL ha))⟩, hxa, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (⟨x * a⁻¹, L.mul_mem x.2 (L.inv_mem (hAL ha))⟩ : L)⁻¹ * x = ⟨a, hAL ha⟩ :=
      Subtype.ext (by simp)
    rw [this]
    exact ha
  have hNL : Group.IsSolvable (N.subgroupOf L) := by
    let f : N.subgroupOf L →* N :=
      MonoidHom.codRestrict (L.subtype.comp (N.subgroupOf L).subtype) N fun x => x.2
    refine Group.isSolvable_of_isSolvable_injective (f := f) fun x y hxy => ?_
    have h : ((x : L) : H) = ((y : L) : H) := congrArg (fun z : N => (z : H)) hxy
    exact Subtype.ext (Subtype.ext h)
  have hsol : Group.IsSolvable ((P.subgroupOf L).map π) := by
    have : Group.IsSolvable ((N.subgroupOf L).map π) :=
      Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hsub)
  have hperf : Group.IsPerfect ((P.subgroupOf L).map π) := by
    have : Group.IsPerfect (P.subgroupOf L) := by
      have := hP
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hPL).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPL).symm.surjective
    exact Group.IsPerfect.ofSurjective (π.subgroupMap_surjective _)
  have hbot := eq_bot_of_isPerfect_of_isSolvable hperf hsol
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  intro x hx
  have hx' : (⟨x, hPL hx⟩ : L) ∈ P.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
  exact Subgroup.mem_subgroupOf.mp (hbot hx')

theorem le_of_isPerfect_of_le_sup_of_isSubnormal {H : Type*} [Group H] {U N P : Subgroup H}
    [N.Normal] (hNsol : Group.IsSolvable N) (hU : U.IsSubnormal) (hP : Group.IsPerfect P)
    (hPU : P ≤ U ⊔ N) : P ≤ U := by
  induction hU with
  | top => exact le_top
  | step A L hAL _ hAn ih =>
    have hPL : P ≤ L := ih (hPU.trans (sup_le_sup_right hAL N))
    exact le_of_isPerfect_of_le_sup_of_subgroupOf_normal hAL hAn hNsol hP hPL hPU

theorem theta_component_subnormal_subgroup_dichotomy {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {Y U : Subgroup H} (hY : Y ∈ thetaComponents p H) (hU : U.IsSubnormal) :
    Y ≤ U ∨ (U ≤ Subgroup.normalizer (Y : Set H) ∧
      ⁅Y, U⁆ ≤ inSubgroup (aschbacherSolvableCore p) Y) := by
  set N := aschbacherSolvableCore p H
  set π := QuotientGroup.mk' N
  have hJ : IsComponent (Y.map π) := isComponent_map_of_mem_thetaComponents hp hY
  have hNsol : Group.IsSolvable N := (solvable_prime_complement_core_characterization hp).1
  rcases LocalCores.component_subnormal_subgroup hJ (hU.map (QuotientGroup.mk'_surjective N))
    with h | h
  · left
    have hYUN : Y ≤ U ⊔ N := by
      have := Subgroup.map_le_iff_le_comap.mp h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
    exact le_of_isPerfect_of_le_sup_of_isSubnormal hNsol hU hY.1 hYUN
  · right
    have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hcomm : ∀ y ∈ Y, ∀ u ∈ U, π u * π y = π y * π u := fun y hy u hu =>
      Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hy)) (π u)
        (Subgroup.mem_map_of_mem π hu)
    have hnorm : U ≤ Subgroup.normalizer (Y : Set H) := by
      intro u hu
      have hσY := map_mulEquiv_mem_thetaComponents hp (MulAut.conj u) hY
      have himage : (Y.map (MulAut.conj u).toMonoidHom).map π = Y.map π := by
        rw [Subgroup.map_map]
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y, hy, ?_⟩
          simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
            MulAut.conj_apply, map_mul, map_inv]
          rw [hcomm y hy u hu, mul_inv_cancel_right]
        · rintro ⟨y, hy, rfl⟩
          refine ⟨y, hy, ?_⟩
          simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
            MulAut.conj_apply, map_mul, map_inv]
          rw [hcomm y hy u hu, mul_inv_cancel_right]
      have heq : Y.map (MulAut.conj u).toMonoidHom = Y :=
        (theta_component_quotient_correspondence (H := H) hp).1.injOn hσY hY himage
      rw [Subgroup.mem_normalizer_iff_conj_image_eq]
      have := congrArg (fun K : Subgroup H => (K : Set H)) heq
      simpa only [Subgroup.coe_map, MulEquiv.coe_toMonoidHom] using this
    refine ⟨hnorm, ?_⟩
    rw [solvable_prime_complement_core_subnormal_intersection hp hY.2.1, Subgroup.commutator_le]
    intro y hy u hu
    refine ⟨?_, ?_⟩
    · have hconj : u * y⁻¹ * u⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hnorm hu) y⁻¹).mp (Y.inv_mem hy)
      have heq : ⁅y, u⁆ = y * (u * y⁻¹ * u⁻¹) := by group
      rw [heq]
      exact Y.mul_mem hy hconj
    · show ⁅y, u⁆ ∈ N
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact (hcomm y hy u hu).symm

end CFSG.RankThree.GroupTheory

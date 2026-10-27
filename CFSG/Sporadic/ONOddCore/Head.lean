module

public import CFSG.Sporadic.ONOddCore.FullGroup
public import CFSG.Sporadic.ONOddCore.FixedRankOne
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFourGroup

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open UnbalancedCatalog.EvenCatalog (oddCore_eq_bot_of_mulEquiv)

section Outer

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem fixed_conjNormal_map (z : X) :
    haveI := genFitting_normal (X := X)
    (fixedSubgroup (MulAut.conjNormal z : MulAut (CFSG.generalizedFitting X))).map
      (CFSG.generalizedFitting X).subtype =
        CFSG.generalizedFitting X ⊓ Subgroup.centralizer {z} := by
  have := genFitting_normal (X := X)
  ext x
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hf' : ((MulAut.conjNormal z f : CFSG.generalizedFitting X) : X) = f :=
      congrArg Subtype.val (show MulAut.conjNormal z f = f from hf)
    rw [MulAut.conjNormal_apply] at hf'
    refine Subgroup.mem_inf.2 ⟨f.2, ?_⟩
    rw [Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
    calc (f : X) * z = z * (f : X) * z⁻¹ * z := by rw [hf']
      _ = z * f := by group
  · intro hx
    obtain ⟨hxF, hxz⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxz
    refine ⟨⟨x, hxF⟩, ?_, rfl⟩
    show MulAut.conjNormal z ⟨x, hxF⟩ = ⟨x, hxF⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    show z * x * z⁻¹ = x
    rw [← hxz]
    group

theorem oddCore_outer_involution
    (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (e : CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.ON) {z : X} (hz2 : orderOf z = 2)
    (hzF : z ∉ CFSG.generalizedFitting X) :
    CFSG.oddCore (Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  have := genFitting_normal (X := X)
  set ψ : CFSG.generalizedFitting X ≃* Pv := e.trans onEquivPv
  set β : MulAut (CFSG.generalizedFitting X) := MulAut.conjNormal z with hβ
  set α : MulAut Pv := MulAut.congr ψ β with hα
  have hβout : β ∉ (MulAut.conj : CFSG.generalizedFitting X →* MulAut _).range := by
    intro h
    apply hzF
    rw [← ker_outerHom hF ψ, MonoidHom.mem_ker, outerHom, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact h
  have hαout : α ∉ (MulAut.conj : Pv →* MulAut Pv).range := by
    rintro ⟨p, hp⟩
    apply hβout
    refine ⟨ψ.symm p, ?_⟩
    have h1 := OuterAutomorphisms.congr_conj ψ.symm p
    rw [hp] at h1
    rw [← h1]
    ext x
    simp [hα, MulAut.congr_apply]
  have hzz : z * z = 1 := by
    rw [← pow_two, ← hz2]
    exact pow_orderOf_eq_one z
  have hβ2 : β * β = 1 := by
    rw [hβ, ← map_mul, hzz, map_one]
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul, hβ2, map_one]
  obtain ⟨⟨V, hVH, hVel, hV4⟩, -⟩ :=
    glq_sporadic_outer_involution_fixed_rank_one_ON_exclusion (L := Pv) ⟨onEquivPv.symm⟩ α hα2
  have eA : (V.subgroupOf (fixedSubgroup α)) ≃* V := Subgroup.subgroupOfEquivOfLe hVH
  have : CFSG.IsElementaryAbelian 2 V := hVel
  have : CFSG.IsElementaryAbelian 2 (V.subgroupOf (fixedSubgroup α)) :=
    isElementaryAbelian_of_mulEquiv eA
  have hA4 : Nat.card (V.subgroupOf (fixedSubgroup α)) = 4 := by
    rw [Nat.card_congr eA.toEquiv, hV4]
  have hH : CFSG.oddCore (fixedSubgroup α) = ⊥ := by
    refine SmallLocal.four_group_local_centralizer_odd_core_vanishing
      (V.subgroupOf (fixedSubgroup α)) hA4 fun a ha ha1 => ?_
    have haV : (a : Pv) ∈ V := Subgroup.mem_subgroupOf.1 ha
    have hsq : (a : Pv) ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := V) _ haV
    have ha1' : (a : Pv) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hord : orderOf (a : Pv) = 2 := orderOf_eq_prime hsq ha1'
    have hαa : α a = a := a.2
    exact oddCore_eq_bot_of_mulEquiv (centralizerSubtypeEquiv (fixedSubgroup α) a).symm
      (oddCore_fixed_centralizer hαout hα2 hord hαa)
  have hβfix : CFSG.oddCore (fixedSubgroup β) = ⊥ :=
    oddCore_eq_bot_of_mulEquiv (fixedCongr ψ β).symm hH
  have e2 := (Subgroup.equivMapOfInjective (fixedSubgroup β) _
    (CFSG.generalizedFitting X).subtype_injective).trans
      (MulEquiv.subgroupCongr (fixed_conjNormal_map z))
  exact oddCore_centralizer_of_inf hF e (oddCore_eq_bot_of_mulEquiv e2 hβfix)

end Outer

theorem ctuc_on_generalized_fitting_involution_centralizer_odd_core_trivial
    {X : Type*}
    [Group X] [Finite X] (hF : IsSimpleGroup (CFSG.generalizedFitting X))
    (hON : Nonempty (CFSG.generalizedFitting X ≃* Blueprint.NativeSporadic.ON)) :
    (CFSG.generalizedFitting X).index ∣ 4 ∧
      ∀ z : X, orderOf z = 2 → CFSG.oddCore (Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  obtain ⟨hidx, hin⟩ := ctu_on_full_group_inner_involution_odd_core hF hON
  obtain ⟨e⟩ := hON
  refine ⟨hidx, fun z hz => ?_⟩
  by_cases hzF : z ∈ CFSG.generalizedFitting X
  · exact hin z hzF hz
  · exact oddCore_outer_involution hF e hz hzF

end CFSG.Sporadic.ONOddCore

module

import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasAFaithful
import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.GroupTheory.SteinbergCEThetaQuotientAction

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

theorem aschbacherSolvableCore_le_center_of_isQuasisimple {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hK : CFSG.IsQuasisimple K) :
    aschbacherSolvableCore p K ≤ Subgroup.center K := by
  rcases LocalCores.quasisimple_normal_subgroups hK
    (inferInstance : (aschbacherSolvableCore p K).Normal) with h | h
  · exfalso
    have hsol : Group.IsSolvable (aschbacherSolvableCore p K) :=
      (solvable_prime_complement_core_characterization (H := K) hp).1
    rw [h] at hsol
    have hsolK : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.topEquiv (G := K)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := K)).symm.injective
    have := hK.1
    have := LocalCores.isQuasisimple_nontrivial hK
    exact Group.IsPerfect.not_isSolvable _ hsolK
  · exact h

theorem mem_centralizer_of_mem_thetaQuotientCentralizer_of_isQuasisimple {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) {A K : Subgroup G} (hK : CFSG.IsQuasisimple K) {x : G}
    (hx : x ∈ thetaQuotientCentralizer p A K) : x ∈ Subgroup.centralizer (K : Set G) := by
  obtain ⟨-, hxN, hxθ⟩ := mem_thetaQuotientCentralizer_iff.mp hx
  have hperf : Group.IsPerfect K := hK.1
  set α : MulAut K := K.normalizerMonoidHom ⟨x, hxN⟩ with hα
  have hαk : ∀ k : K, ((α k : K) : G) = x * k * x⁻¹ := fun k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨x, hxN⟩ k
  have hcentral : ∀ k : K, k⁻¹ * α k ∈ Subgroup.center K := by
    intro k
    obtain ⟨y, hy, hyeq⟩ := hxθ k k.2
    have hyc : y ∈ Subgroup.center K :=
      aschbacherSolvableCore_le_center_of_isQuasisimple hp hK hy
    have hyeq' : (y : G) = x * k * x⁻¹ * (k : G)⁻¹ := hyeq
    have hαy : α k = y * k := Subtype.ext (by
      rw [hαk, Subgroup.coe_mul, hyeq']
      group)
    rw [hαy, ← mul_assoc, Subgroup.mem_center_iff.mp hyc k⁻¹, mul_assoc, inv_mul_cancel,
      mul_one]
    exact hyc
  have h1 : α = 1 :=
    CFSG.ComponentClassification.CentralCover.eq_one_of_forall_inv_mul_mem_center α hcentral
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have h2 := congrArg (fun φ : MulAut K => ((φ ⟨g, hg⟩ : K) : G)) h1
  simp only [hαk, MulAut.one_apply] at h2
  calc g * x = (x * g * x⁻¹) * x := by rw [h2]
    _ = x * g := by group

theorem thetaQuotientCentralizer_eq_inf_centralizer_of_isQuasisimple {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : p.Prime) {A K : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hK : CFSG.IsQuasisimple K) :
    thetaQuotientCentralizer p A K = A ⊓ Subgroup.centralizer (K : Set G) := by
  ext x
  refine ⟨fun hx => ⟨(mem_thetaQuotientCentralizer_iff.mp hx).1,
    mem_centralizer_of_mem_thetaQuotientCentralizer_of_isQuasisimple hp hK hx⟩,
    fun ⟨hxA, hxC⟩ => mem_thetaQuotientCentralizer_iff.mpr ⟨hxA, hAK hxA, fun k hk => ?_⟩⟩
  have h : x * k = k * x := (Subgroup.mem_centralizer_iff.mp hxC k hk).symm
  have : x * k * x⁻¹ * k⁻¹ = 1 := by
    rw [h]
    group
  rw [this]
  exact Subgroup.one_mem _

theorem eq_of_isSubnormal_of_isPerfect_of_isQuasisimple {G : Type*} [Group G] [Finite G]
    {K P : Subgroup G} (hK : CFSG.IsQuasisimple K) (hPK : P ≤ K) (hP : Group.IsPerfect P)
    (hP1 : P ≠ ⊥) (hsn : (P.subgroupOf K).IsSubnormal) : P = K := by
  have hcomp : CFSG.IsComponent (⊤ : Subgroup K) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := K)).symm hK,
      Subgroup.IsSubnormal.top⟩
  rcases LocalCores.component_subnormal_subgroup hcomp hsn with h | h
  · refine le_antisymm hPK fun x hx => ?_
    exact h (Subgroup.mem_top (⟨x, hx⟩ : K))
  · exfalso
    have hz : P.subgroupOf K ≤ Subgroup.center K :=
      Subgroup.commutator_top_left_eq_bot_iff_le_center.mp h
    have hPc : ⁅P, P⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha b hb
      have := Subgroup.mem_center_iff.mp (hz (show (⟨a, hPK ha⟩ : K) ∈ P.subgroupOf K from ha))
        ⟨b, hPK hb⟩
      exact congrArg Subtype.val this
    exact hP1 (by rw [← Subgroup.isPerfect_iff.mp hP, hPc])

end CFSG.RankThree.PartOne

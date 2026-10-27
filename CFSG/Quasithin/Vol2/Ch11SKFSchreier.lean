module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZH
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem exists_mul_mem_centralizer_of_schreier (hS : SchreierFor CFSG.Blueprint.Catalog)
    {G : Type} [Group G] [Finite G] {J P : Subgroup G}
    (hJ : CFSG.GorensteinWalter.IsQuasisimple ↥J)
    (hcat : CFSG.Blueprint.Catalog (↥J ⧸ Subgroup.center ↥J)) (hP : ⁅P, P⁆ = P)
    (hPN : P ≤ Subgroup.normalizer (J : Set G)) {ℓ : G} (hℓ : ℓ ∈ P) :
    ∃ j ∈ J, j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G) := by
  obtain ⟨-, hcomm, hsimp⟩ := hJ
  have : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hcomm
  have : Group.IsPerfect ↥P := by
    rw [Group.isPerfect_def, eq_top_iff]
    intro x _
    have hx : (x : G) ∈ ⁅P, P⁆ := hP.symm ▸ x.2
    rw [← Subgroup.map_subtype_commutator] at hx
    exact (Subgroup.mem_map_iff_mem P.subtype_injective).mp hx
  have hnab : ∃ a b : ↥J ⧸ Subgroup.center ↥J, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    obtain ⟨a, b, hne⟩ := hsimp.exists_pair_ne
    have hle : commutator ↥J ≤ Subgroup.center ↥J := by
      rw [← QuotientGroup.ker_mk' (Subgroup.center ↥J), _root_.commutator_def,
        ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, eq_bot_iff]
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨c, -, d, -, rfl⟩ := hz
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hab c d
      | one => exact Subgroup.one_mem _
      | mul y z _ _ hy hz => exact Subgroup.mul_mem _ hy hz
      | inv y _ hy => exact Subgroup.inv_mem _ hy
    rw [hcomm] at hle
    have htriv : ∀ q : ↥J ⧸ Subgroup.center ↥J, q = 1 := fun q => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      rw [QuotientGroup.eq_one_iff]
      exact hle trivial
    exact hne ((htriv a).trans (htriv b).symm)
  have : Group.IsSolvable (Outer (↥J ⧸ Subgroup.center ↥J)) := hS _ hnab hcat
  have : Group.IsSolvable (Outer ↥J) := solvable_of_centerQuotient ↥J
  obtain ⟨j, hj⟩ := perfect_action_inner
    (J.normalizerMonoidHom.comp (Subgroup.inclusion hPN)) ⟨ℓ, hℓ⟩
  refine ⟨j, j.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
  have h1 := congrArg (fun a : MulAut ↥J => ((a ⟨x, hx⟩ : ↥J) : G)) hj
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
  calc x * ((j : G)⁻¹ * ℓ) = (j : G)⁻¹ * ((j : G) * x * (j : G)⁻¹) * ℓ := by group
    _ = (j : G)⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ := by rw [h1]
    _ = (j : G)⁻¹ * ℓ * x := by group

theorem factSchreierComp_of (hS : SchreierFor CFSG.Blueprint.Catalog) : FactSchreierComp := by
  intro G _ _ _ _ _ X₁ J P _ hJ hcat hP _ hPJ ℓ hℓ
  exact exists_mul_mem_centralizer_of_schreier hS hJ.2.2 hcat hP hPJ hℓ

end CFSG.Quasithin.Vol2.Ch11.SecS

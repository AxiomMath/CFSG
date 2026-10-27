module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryExcludedSetup

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open scoped commutatorElement

variable {G : Type} [Group G] {H : Subgroup G} {z : G} {beta : rightCosetSpace H} {t u : G}
  {A P : Subgroup G} (d : ExclusionSetup H z beta t u A P)

namespace ExclusionSetup

theorem fst_eq_zero_of_commute_torusElt {c : normOne d.Fu.J}
    (hc : ((c : d.Fu.kˣ) : d.Fu.k) ^ 3 ≠ 1) {w : hermitianUnipotentCoord d.Fu.J}
    (hw : torusElt d.Fu c * d.Fu.rootHom w = d.Fu.rootHom w * torusElt d.Fu c) : w.1.1 = 0 := by
  have h := torusElt_conj d.Fu c w
  rw [hw, mul_inv_cancel_right] at h
  have h' := congrArg (fun v : hermitianUnipotentCoord d.Fu.J => v.1.1)
    (d.Fu.rootHom_injective h)
  change w.1.1 = ((c : d.Fu.kˣ) : d.Fu.k) ^ 3 * w.1.1 at h'
  have h0 : (((c : d.Fu.kˣ) : d.Fu.k) ^ 3 - 1) * w.1.1 = 0 := by linear_combination -h'
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc)

theorem mem_point_of_mem_root_of_commute {x : G} (hxT : x ∈ d.Fu.root)
    (hxA : x ∈ Subgroup.centralizer (A : Set G)) :
    x ∈ minimalLocalFailurePairActionPointHull H z := by
  obtain ⟨c, hc, hcA⟩ := d.exists_torus_noncentral
  obtain ⟨w, rfl⟩ := hxT
  exact (rootHom_mem_iff d.Fu w).mpr
    (d.fst_eq_zero_of_commute_torusElt hc (Subgroup.mem_centralizer_iff.mp hxA _ hcA))

theorem exists_commutator_fst (a' : d.Fu.k) :
    ∃ v : hermitianUnipotentCoord d.Fu.J, d.Fu.rootHom v ∈ ⁅d.Fu.root, A⁆ ∧ v.1.1 = a' := by
  obtain ⟨c, hc, hcA⟩ := d.exists_torus_noncentral
  set μ := ((c : d.Fu.kˣ) : d.Fu.k) ^ 3
  have hμ : 1 - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  obtain ⟨v, hv⟩ := exists_fst_eq d.Fu.J (2 ^ d.Fu.f) d.Fu.hcard d.Fu.hfixed ((1 - μ)⁻¹ * a')
  refine ⟨v * torusCoord c v⁻¹, ?_, ?_⟩
  · have hcomm : ⁅d.Fu.rootHom v, torusElt d.Fu c⁆ = d.Fu.rootHom (v * torusCoord c v⁻¹) := by
      rw [commutatorElement_def, map_mul, ← torusElt_conj, map_inv]
      group
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator ⟨v, rfl⟩ hcA
  · change v.1.1 + μ * (-v.1.1) = a'
    rw [hv]
    field_simp
    ring

theorem root_le_commutator : d.Fu.root ≤ ⁅d.Fu.root, A⁆ := by
  have hfst := d.exists_commutator_fst
  have hQ : ∀ w : hermitianUnipotentCoord d.Fu.J, w.1.1 = 0 →
      d.Fu.rootHom w ∈ ⁅d.Fu.root, A⁆ := by
    intro w hw0
    obtain ⟨b, hb⟩ := exists_trace_eq d.Fu.J (2 ^ d.Fu.f) d.Fu.hcard d.Fu.hfixed
      (conj_snd_of_fst_eq_zero d.Fu.J hw0)
    obtain ⟨v₁, hv₁, hv₁1⟩ := hfst 1
    obtain ⟨v₂, hv₂, hv₂1⟩ := hfst b
    have heq : ⁅v₁, v₂⁆ = w := coord_ext (by rw [fst_commutator, hw0])
      (by rw [snd_commutator, hv₁1, hv₂1, map_one, mul_one, one_mul, ← hb, add_comm])
    rw [← heq, map_commutatorElement, commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hv₁ hv₂)
      (Subgroup.inv_mem _ hv₁)) (Subgroup.inv_mem _ hv₂)
  rintro _ ⟨w, rfl⟩
  obtain ⟨v, hv, hvw⟩ := hfst w.1.1
  have hq : (v⁻¹ * w).1.1 = 0 := by rw [fst_mul, fst_inv, hvw, neg_add_cancel]
  have h := Subgroup.mul_mem _ hv (hQ _ hq)
  rwa [← map_mul, mul_inv_cancel_left] at h

end ExclusionSetup

end CFSG.ShultStronglyClosedTI.UnitaryExcluded

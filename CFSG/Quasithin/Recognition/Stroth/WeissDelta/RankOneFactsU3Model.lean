module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneLocalU32

public section

open scoped Pointwise

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth
open CFSG.ProperTwoGeneratedCore.RootCenter

theorem torusPSU_transitive_rootCenter {K : Type} [Field K] [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : ℕ) (hcard : Nat.card K = (2 ^ k) ^ 2)
    (hfixed : Nat.card {z : K // J.conj z = z} = 2 ^ k) :
    ∀ u v : unitaryRootCenter J hJ, u ≠ 1 → v ≠ 1 →
      ∃ t ∈ (torusPSU J hJ).range, t * (u : ProjectiveSpecialUnitaryMatrixGroup J) * t⁻¹ =
        (v : ProjectiveSpecialUnitaryMatrixGroup J) := by
  classical
  have hcenterOf (u : ↥(unitaryRootCenter J hJ)) :
      CFSG.ProperTwoGeneratedCore.TheoremC.InCenterOf (unitaryCoverRoot J hJ)
        (u : ProjectiveSpecialUnitaryMatrixGroup J) := by
    rw [CFSG.ProperTwoGeneratedCore.TheoremC.inCenterOf_unitaryCoverRoot_iff
      J hcard hfixed hJ]
    obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.mp u.2
    refine ⟨z, ?_, hzu⟩
    have hz0 : Multiplicative.ofAdd z.1.1 = (1 : Multiplicative K) := hz
    exact (Multiplicative.ofAdd (α := K)).injective (by simpa using hz0)
  intro u v hu1 hv1
  obtain ⟨d, hd, hdconj⟩ :=
    CFSG.ProperTwoGeneratedCore.TheoremC.unitaryCoverTorus_transitive_center
      J hcard hfixed hJ (hcenterOf u) (fun h => hu1 (Subtype.ext h))
      (hcenterOf v) (fun h => hv1 (Subtype.ext h))
  refine ⟨d⁻¹, ?_, ?_⟩
  · rw [CFSG.ShultStronglyClosedTI.UnitaryModel.range_torusPSU]
    exact (unitaryCoverTorus J hJ).inv_mem hd
  · simpa using hdconj

theorem center_unitaryRootCenter_eq {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [Field F] [Finite F] {N : Subgroup X} {k : ℕ} (hk : 2 ≤ k)
    (hF : Nat.card F = (2 ^ k) ^ 2) (M : PSU3IsotropicModel X Ω F N k) :
    {x : ↥N | x ∈ M.U' ∧ ∀ y ∈ M.U', x * y = y * x} =
      ((unitaryRootCenter M.J M.hJ).map M.eN.symm.toMonoidHom : Set ↥N) := by
  classical
  have hcenter := (unitaryRootCenterAutomorphisms M.J k hk hF M.hfixed M.hJ).center_iff
  have hroot : M.U' = (unitaryCoverRoot M.J M.hJ).map M.eN.symm.toMonoidHom := by
    rw [M.hU']
    rfl
  ext x
  constructor
  · rintro ⟨hxU', hxcomm⟩
    have hxroot : M.eN x ∈ unitaryCoverRoot M.J M.hJ := by
      rw [hroot] at hxU'
      rw [Subgroup.mem_map_equiv] at hxU'
      simpa using hxU'
    have hxcomm' : ∀ y ∈ unitaryCoverRoot M.J M.hJ, M.eN x * y = y * M.eN x := by
      intro y hy
      have hy' : M.eN.symm y ∈ M.U' := by
        rw [hroot]
        exact Subgroup.mem_map_of_mem _ hy
      have h := hxcomm (M.eN.symm y) hy'
      have h' := congrArg M.eN h
      simpa using h'
    have hxcenter : M.eN x ∈ unitaryRootCenter M.J M.hJ :=
      (hcenter (M.eN x)).mpr ⟨hxroot, hxcomm'⟩
    change x ∈ Subgroup.map M.eN.symm.toMonoidHom (unitaryRootCenter M.J M.hJ)
    rw [Subgroup.mem_map_equiv]
    simpa using hxcenter
  · intro hxmap
    change x ∈ Subgroup.map M.eN.symm.toMonoidHom (unitaryRootCenter M.J M.hJ) at hxmap
    rw [Subgroup.mem_map_equiv] at hxmap
    have hxcenter := (hcenter (M.eN x)).mp hxmap
    constructor
    · rw [hroot]
      rw [Subgroup.mem_map_equiv]
      simpa using hxcenter.1
    · intro y hy
      have hyroot : M.eN y ∈ unitaryCoverRoot M.J M.hJ := by
        rw [hroot] at hy
        rw [Subgroup.mem_map_equiv] at hy
        simpa using hy
      have h := hxcenter.2 (M.eN y) hyroot
      have h' := congrArg M.eN.symm h
      simpa using h'

end CFSG.Quasithin.Stroth.WeissDelta

end

module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Defs

import Mathlib.Algebra.Group.Subgroup.Actions

open scoped Pointwise

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

private theorem smul_mem_fixedPointSubgroup_of_mem_normalizer {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {S : Subgroup ↥H} {g : ↥H}
    (hg : g ∈ Subgroup.normalizer (S : Set ↥H)) {x : W}
    (hx : x ∈ (CFSG.fixedPointSubgroup ↥S W : Subgroup W)) :
    g • x ∈ (CFSG.fixedPointSubgroup ↥S W : Subgroup W) := by
  rw [FixedPoints.mem_subgroup] at hx ⊢
  intro s
  have hmem : g⁻¹ * (s : ↥H) * g ∈ S :=
    ((Subgroup.mem_normalizer_iff'' (H := S)).mp hg (s : ↥H)).mp s.2
  have hux : (g⁻¹ * (s : ↥H) * g : ↥H) • x = x := by
    have h := hx (⟨g⁻¹ * (s : ↥H) * g, hmem⟩ : ↥S)
    rwa [Subgroup.smul_def] at h
  calc
    s • (g • x) = ((s : ↥H) * g) • x := by rw [Subgroup.smul_def, mul_smul]
    _ = (g * (g⁻¹ * (s : ↥H) * g)) • x := by
          rw [show g * (g⁻¹ * (s : ↥H) * g) = (s : ↥H) * g by
                rw [mul_assoc, mul_inv_cancel_left]]
    _ = g • ((g⁻¹ * (s : ↥H) * g) • x) := by rw [mul_smul]
    _ = g • x := by rw [hux]

theorem normalizer_le_stabilizer_fixedPointSubgroup {W : Type} [CommGroup W]
    (H : Subgroup (MulAut W)) (S : Subgroup ↥H) :
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    letI : MulDistribMulAction ↥S W := MulDistribMulAction.compHom W (H.subtype.comp S.subtype)
    Subgroup.normalizer (S : Set ↥H) ≤
      MulAction.stabilizer ↥H ((CFSG.fixedPointSubgroup ↥S W : Subgroup W) : Set W) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff]
  apply le_antisymm
  · intro y hy
    rw [Set.mem_smul_set] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact smul_mem_fixedPointSubgroup_of_mem_normalizer hg hx
  · intro y hy
    rw [Set.mem_smul_set]
    exact ⟨g⁻¹ • y, smul_mem_fixedPointSubgroup_of_mem_normalizer (Subgroup.inv_mem _ hg) hy,
      smul_inv_smul g y⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

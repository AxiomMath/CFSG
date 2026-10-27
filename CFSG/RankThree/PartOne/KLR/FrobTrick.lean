module

public import CFSG.RankThree.PartOne.KE.SigmaCentralizer
public import CFSG.LieType.Chevalley.DiagonalFieldActorData

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
open scoped Pointwise

variable {τ : Tag} {L : Type} [Field L]

theorem map_entrywise_rootSpan (σ : L ≃+* L) (S : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ L S).map (Units.map (entrywiseHom σ.toRingHom)) = rootSpan τ L S := by
  rw [rootSpan, Subgroup.map_iSup]
  refine iSup_congr fun α => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun _ => map_entrywise_rootSubgroup σ α

theorem units_map_entrywiseHom_torus_eq_sq (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2) {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) : Units.map (entrywiseHom σ.toRingHom) h = h * h := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv, ← rootDiagUnit_mul]
  congr 1
  funext i
  refine Units.ext ?_
  simp [hσ, sq]

theorem mem_rootSpan_of_mul_self_mem (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2) {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) {S : Set (Fin τ.rank → ℤ)} (hS : h * h ∈ rootSpan τ L S) :
    h ∈ rootSpan τ L S := by
  have hmap := map_entrywise_rootSpan (τ := τ) σ S
  have hε : Units.map (entrywiseHom σ.toRingHom) h ∈ (rootSpan τ L S).map
      (Units.map (entrywiseHom σ.toRingHom)) := by
    rw [hmap, units_map_entrywiseHom_torus_eq_sq σ hσ hh]
    exact hS
  obtain ⟨u, hu, hue⟩ := hε
  have hinj : Function.Injective (Units.map (entrywiseHom σ.toRingHom) : ModGL τ L → ModGL τ L) :=
    Units.map_injective (f := entrywiseHom σ.toRingHom) (entrywise_injective σ.toRingHom)
  rw [← hinj hue]
  exact hu

theorem mem_rootSpan_of_mul_self_eq_one (σ : L ≃+* L) (hσ : ∀ c, σ c = c ^ 2)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {g : ModGL τ L}
    (hg : g ∈ (torusGroup τ L : Set (ModGL τ L)) * (rootSpan τ L S : Set (ModGL τ L)))
    (hg2 : g * g = 1) : g ∈ rootSpan τ L S := by
  obtain ⟨h, hh, u, hu, rfl⟩ := hg
  have hnorm := torusGroup_le_normalizer_rootSpan (τ := τ) (L := L) hS
  have hconj : h⁻¹ * u * h ∈ rootSpan τ L S := by
    have := (Subgroup.mem_normalizer_iff.1 (hnorm (inv_mem hh)) u).1 hu
    simpa using this
  have hsq : h * h ∈ rootSpan τ L S := by
    have h1 : h * u * (h * u) = (h * h) * (h⁻¹ * u * h * u) := by group
    rw [h1] at hg2
    have h2 : (h * h) = (h⁻¹ * u * h * u)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hg2
    rw [h2]
    exact inv_mem (mul_mem hconj hu)
  have hhS := mem_rootSpan_of_mul_self_mem σ hσ hh hsq
  exact mul_mem hhS hu

end CFSG.RankThree.PartOne.KLR

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open

variable {G : Type} [Group G]

theorem centSection_conj_mem {M A B : Subgroup G}
    (hAM : M ≤ Subgroup.normalizer (A : Set G))
    (hBM : M ≤ Subgroup.normalizer (B : Set G))
    {g c : G} (hg : g ∈ M) (hc : c ∈ centSection M A B) :
    g * c * g⁻¹ ∈ centSection M A B := by
  rcases hc with ⟨hcM, hcA, hcB, hcomm⟩
  have hgA : g ∈ Subgroup.normalizer (A : Set G) := hAM hg
  have hgB : g ∈ Subgroup.normalizer (B : Set G) := hBM hg
  refine ⟨M.mul_mem (M.mul_mem hg hcM) (M.inv_mem hg), ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgA hcA) (Subgroup.inv_mem _ hgA)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgB hcB) (Subgroup.inv_mem _ hgB)
  · intro a ha
    have hga : g⁻¹ * a * g ∈ A := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgA) a).mp ha
    have hinner : c * (g⁻¹ * a * g) * c⁻¹ * (g⁻¹ * a * g)⁻¹ ∈ B := hcomm _ hga
    have hconj : g * (c * (g⁻¹ * a * g) * c⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp hgB _).mp hinner
    have heq : (g * c * g⁻¹) * a * (g * c * g⁻¹)⁻¹ * a⁻¹ =
        g * (c * (g⁻¹ * a * g) * c⁻¹ * (g⁻¹ * a * g)⁻¹) * g⁻¹ := by group
    rwa [heq]

theorem centSection_le_normalizer {M L : Subgroup G}
    (hNL : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer (centSection M L (pCoreOf 2 L) : Set G) := by
  have hBL : M ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    fun x hx => CFSG.PreuniquenessRankFour.Helpers.normalizer_le_normalizer_characteristic
      (pCore 2 ↥L) (CFSG.pCore_characteristic (p := 2) (G := ↥L)) (hNL hx)
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact centSection_conj_mem hNL hBL hm hc
  · intro hc
    have hm' : m⁻¹ ∈ M := M.inv_mem hm
    have h := centSection_conj_mem hNL hBL hm' hc
    have heq : m⁻¹ * (m * c * m⁻¹) * (m⁻¹)⁻¹ = c := by group
    rw [heq] at h
    exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

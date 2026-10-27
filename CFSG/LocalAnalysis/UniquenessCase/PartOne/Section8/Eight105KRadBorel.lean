module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105KRadSetup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LinearGroups (stdHermForm)
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {K : Type} [Field K] {f : ℕ}

private theorem exists_isotropic_normalizer_le_aux (K : Type) [Field K] (f : ℕ) [Finite K]
    [CharP K 2] {r ε : ℕ} (h : UnitaryFieldData 2 f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (T₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K)) :
    ∃ L : Submodule K (Fin (2 * r + ε) → K), Module.finrank K L = r ∧
      (∀ v ∈ L, ∀ w ∈ L, stdHermForm h (2 * r + ε) v w = 0) ∧
      normalizer ((T₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
        Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤
        stabSU (2 ^ f) L := by
  classical
  obtain ⟨R, hR⟩ := exists_isHypTransport h (r := r) (ε := ε)
  set φ : hypSU h r ε ≃* StatedSU (2 * r + ε) (2 ^ f) K := hypTransport h hR with hφ
  let T : Sylow 2 (hypSU h r ε) :=
    Sylow.mapSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective T₀
  have hTc : (T : Subgroup (hypSU h r ε)) = (T₀ : Subgroup _).map φ.symm.toMonoidHom := rfl
  obtain ⟨U', hU'⟩ := (unitary_order_and_Sylow h hr hε).2.1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (hypSU h r ε) U' T
  have hTsub : (T : Subgroup (hypSU h r ε)) =
      MulAut.conj g • (U' : Subgroup (hypSU h r ε)) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have hNT : Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set _) =
      (Subgroup.normalizer ((U' : Subgroup (hypSU h r ε)) : Set _)).map
        (MulAut.conj g).toMonoidHom := by
    rw [hTsub]
    exact (Subgroup.map_equiv_normalizer_eq _ (MulAut.conj g)).symm
  refine ⟨transportSubspace h hR (g • hypFlag h r ε r), ?_, ?_, ?_⟩
  · rw [finrank_transportSubspace hR, finrank_smul g,
      (isIsotropicChain_hypFlag h (r := r) hε).1 r le_rfl]
  · exact (isTotallyIsotropic_transportSubspace hR _).mp
      (smul_isotropic g ((isIsotropicChain_hypFlag h (r := r) hε).2.2 r le_rfl))
  · intro y hy
    rw [mem_stabSU]
    have hzN : φ.symm y ∈ Subgroup.normalizer ((T : Subgroup (hypSU h r ε)) : Set _) := by
      rw [hTc, ← Subgroup.map_equiv_normalizer_eq]
      exact ⟨y, hy, rfl⟩
    rw [hNT] at hzN
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hzN
    have hxB : x ∈ hypBorel h r ε := by
      rw [← normalizer_hypUnitriangular h hr hε]
      simpa [hU'] using hx
    have hxfix : x • hypFlag h r ε r = hypFlag h r ε r :=
      (mem_hypBorel.mp hxB) r hr le_rfl
    have hxz' : φ.symm y = g * x * g⁻¹ := by
      simpa [MulAut.conj_apply] using hxz.symm
    have hzfix : φ.symm y • (g • hypFlag h r ε r) = g • hypFlag h r ε r := by
      rw [hxz', ← mul_smul, show g * x * g⁻¹ * g = g * x by group, mul_smul, hxfix]
    have hzfixL : y • transportSubspace h hR (g • hypFlag h r ε r) =
        transportSubspace h hR (g • hypFlag h r ε r) := by
      have e := transportSubspace_smul hR (φ.symm y) (g • hypFlag h r ε r)
      rw [hzfix, ← hφ, MulEquiv.apply_symm_apply] at e
      exact e.symm
    intro w hw
    exact (CFSG.AGLEmbedding.ToralCensus.smul_eq_iff_mulVec_mem
      (y : GL (Fin (2 * r + ε)) K) _).mp hzfixL w hw

theorem exists_isotropic_normalizer_le (h : UnitaryFieldData 2 f K) {r ε : ℕ} (hr : 1 ≤ r)
    (hε : ε ≤ 1) (T₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K)) :
    ∃ L : Submodule K (Fin (2 * r + ε) → K), Module.finrank K L = r ∧
      (∀ v ∈ L, ∀ w ∈ L, stdHermForm h (2 * r + ε) v w = 0) ∧
      normalizer ((T₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
        Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤
        stabSU (2 ^ f) L :=
  @exists_isotropic_normalizer_le_aux K _ f h.finite h.charP r ε h hr hε T₀

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

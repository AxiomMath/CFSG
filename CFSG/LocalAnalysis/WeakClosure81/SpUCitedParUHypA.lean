module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUBasic
public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParQuotA
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {K : Type} [Field K] {r ε : ℕ}

private theorem spUCited_hypForm_smul_smul {p f : ℕ} (h : UnitaryFieldData p f K) (a b : K)
    (y : HypIndex r ε → K) :
    hypForm h r ε (a • y) (b • y) = h.bar a * b * hypForm h r ε y y := by
  have h1 : hypForm h r ε (a • y) = h.bar a • hypForm h r ε y :=
    LinearMap.map_smulₛₗ (f := hypForm h r ε) a y
  rw [h1, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

private theorem spUCited_exists_smul_of_mem_normalizer {p f : ℕ} (h : UnitaryFieldData p f K)
    {y : HypIndex r ε → K} (hy0 : y ≠ 0) (hy : hypForm h r ε y y = 0)
    (g : ↥(hypSU h r ε))
    (hg : g ∈ Subgroup.normalizer (uCitedRoot h r ε y : Set ↥(hypSU h r ε))) :
    ∃ c : K, c ≠ 0 ∧
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y = c • y := by
  have hinj : Function.Injective (Matrix.mulVec
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit (g : GL (HypIndex r ε) K))
  have hgy0 : ((g : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y ≠ 0 :=
    fun hh => hy0 (hinj (by rw [hh, Matrix.mulVec_zero]))
  have hgyiso : hypForm h r ε
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y)
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) = 0 := by
    have h1 := hypForm_smul_smul h g y y
    simpa [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec, hy] using h1
  have hmap := map_conj_uCitedRoot h g hy
  have hnorm : (uCitedRoot h r ε y).map (MulAut.conj g).toMonoidHom = uCitedRoot h r ε y := by
    simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have heq : uCitedRoot h r ε
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y) =
      uCitedRoot h r ε y := by
    rw [← hmap, hnorm]
  obtain ⟨μ, hμ⟩ := exists_smul_of_uCitedRoot_eq h hgy0 hy0 hgyiso hy heq
  have hμ0 : μ ≠ 0 := fun h0 => hy0 (by rw [hμ, h0, zero_smul])
  have h2 : ((g : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ y = μ⁻¹ • y := by
    have h := congrArg (fun z => μ⁻¹ • z) hμ
    simp only [Matrix.smul_mulVec, inv_smul_smul₀ hμ0] at h
    exact h.symm
  exact ⟨μ⁻¹, inv_ne_zero hμ0, h2⟩

theorem uCited_proj_root_eq_of_normalized {f : ℕ} (h : UnitaryFieldData 2 f K) (hr : 2 ≤ r)
    (hε : ε ≤ 1) {y : HypIndex r ε → K} (hy0 : y ≠ 0) (hy : hypForm h r ε y y = 0)
    (hN : (hypUnitriangular h r ε).map (hypProj h r ε) ≤
      Subgroup.normalizer (((uCitedRoot h r ε y).map (hypProj h r ε) :
        Subgroup (hypPSU h r ε)) : Set (hypPSU h r ε))) :
    (uCitedRoot h r ε y).map (hypProj h r ε) =
      (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))).map
        (hypProj h r ε) := by
  have hX : IsPGroup 2 ↥(uCitedRoot h r ε y) :=
    IsPGroup.of_card (n := f)
      ((card_uCitedRoot h hy0 hy).trans (unitary_field_trace h).2.1)
  have hker : (hypProj h r ε).ker ≤ Subgroup.center ↥(hypSU h r ε) := by
    rw [ker_hypProj]
    exact normOneScalars_le_center h _ _
  have hodd : ¬ 2 ∣ Nat.card (hypProj h r ε).ker := by
    rw [ker_hypProj, card_hypScalars h (by omega)]
    exact not_dvd_gcd_pow_add_one h _
  have hUN : hypUnitriangular h r ε ≤
      Subgroup.normalizer (uCitedRoot h r ε y : Set ↥(hypSU h r ε)) := by
    have h1 := (Subgroup.map_le_iff_le_comap).mp hN
    rwa [spUCited_comap_normalizer_map (hypProj h r ε) (hypProj_surjective h r ε) hker hodd
      (X := uCitedRoot h r ε y) hX] at h1
  have hiso : ∀ x ∈ (Submodule.span K {y} : Submodule K (HypIndex r ε → K)),
      ∀ z ∈ (Submodule.span K {y} : Submodule K (HypIndex r ε → K)),
      hypForm h r ε x z = 0 := by
    intro x hx z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [spUCited_hypForm_smul_smul h a b y, hy, mul_zero]
  have hinv : ∀ u ∈ hypUnitriangular h r ε,
      u • (Submodule.span K {y} : Submodule K (HypIndex r ε → K)) =
        Submodule.span K {y} := by
    intro u hu
    obtain ⟨c, hc0, hc⟩ := spUCited_exists_smul_of_mem_normalizer h hy0 hy u (hUN hu)
    rw [Subgroup.smul_def, smul_eq_map, Submodule.map_span, Set.image_singleton,
      Matrix.mulVecLin_apply, hc]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) y
  obtain ⟨d, hd, hWd⟩ := (unitriangular_invariant_isotropic_subspaces h (by omega) hε).2.2.1
    (Submodule.span K {y}) hiso hinv
  have hfr : Module.finrank K (hypFlag h r ε d) = d := (isIsotropicChain_hypFlag h hε).1 d hd
  have hd1 : d = 1 := by
    rw [← hfr, ← hWd, finrank_span_singleton hy0]
  have hW1 : Submodule.span K {y} = hypFlag h r ε 1 := by rw [hWd, hd1]
  have hy_mem : y ∈ Submodule.span K
      ({Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)} :
        Set (HypIndex r ε → K)) := by
    rw [← (unitriangular_invariant_isotropic_subspaces h (by omega) hε).1, ← hW1]
    exact Submodule.mem_span_singleton_self y
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy_mem
  have hc0 : c ≠ 0 := fun h0 => hy0 (by rw [← hc, h0, zero_smul])
  have hroot : uCitedRoot h r ε y = uCitedRoot h r ε
      (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) : HypIndex r ε → K) := by
    rw [hc.symm, uCitedRoot_smul h (hypForm_single_inl_self h ⟨0, by omega⟩) hc0]
  rw [hroot]

end CFSG.LocalAnalysis.WeakClosure81

end

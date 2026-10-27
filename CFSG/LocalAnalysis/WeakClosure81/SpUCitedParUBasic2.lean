module

public import CFSG.LocalAnalysis.WeakClosure81.SpUCitedParUBasic
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvariant
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherParabolicData
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherReducedWord

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem uCited_root_le_unipotent (h : UnitaryFieldData p f K) (i : Fin r) :
    uCitedRoot h r ε (Pi.single (Sum.inl i) (1 : K)) ≤ hypUnitriangular h r ε := by
  intro x hx
  rw [mem_uCitedRoot h (hypForm_single_inl_self h i)] at hx
  obtain ⟨c, _hc, hM⟩ := hx
  refine mem_hypUnitriangular_of_strict
    (N := Matrix.single (Sum.inl i) (Sum.inr (Sum.inr i)) c) ?_ ?_
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_apply', hM, Matrix.toLin'_apply']
    refine LinearMap.ext fun y => ?_
    rw [hermTransvection_apply, hypForm_single_inl, Matrix.mulVecLin_apply,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
  · intro x y hxy
    obtain ⟨rfl, rfl⟩ := single_ne_zero_imp hxy
    simp only [fullPos_inl, fullPos_inr_inr]
    have hi : (i : ℕ) < r := i.2
    omega

theorem uCited_mem_normalizer_root_iff (h : UnitaryFieldData p f K) (i : Fin r)
    (g : ↥(hypSU h r ε)) :
    g ∈ Subgroup.normalizer (uCitedRoot h r ε (Pi.single (Sum.inl i) (1 : K)) :
        Set ↥(hypSU h r ε)) ↔
      ∃ c : K, c ≠ 0 ∧
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
            (Pi.single (Sum.inl i) (1 : K) : HypIndex r ε → K) =
          c • (Pi.single (Sum.inl i) (1 : K) : HypIndex r ε → K) := by
  set v : HypIndex r ε → K := Pi.single (Sum.inl i) (1 : K) with hvdef
  have h0 : v ≠ 0 := by
    intro hzero
    have := congrFun hzero (Sum.inl i)
    simpa [hvdef] using this
  have hinj : Function.Injective (Matrix.mulVec
      ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :=
    Matrix.mulVec_injective_of_isUnit (Units.isUnit (g : GL (HypIndex r ε) K))
  have hne : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v ≠ 0 :=
    fun hh => h0 (hinj (by rw [hh, Matrix.mulVec_zero]))
  have hvv : hypForm h r ε v v = 0 := by
    simpa [hvdef] using hypForm_single_inl_self h i
  have hiso : hypForm h r ε
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v)
      (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) = 0 := by
    have h1 := hypForm_smul_smul h g v v
    simpa [Subgroup.smul_def, Units.smul_def, Matrix.smul_eq_mulVec, hvv] using h1
  have hmap : (uCitedRoot h r ε v).map (↑(MulAut.conj g)) =
      uCitedRoot h r ε
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ v) :=
    map_conj_uCitedRoot h g hvv
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, hmap]
  constructor
  · intro heq
    obtain ⟨μ, hμ⟩ := exists_smul_of_uCitedRoot_eq h h0 hne hvv hiso heq.symm
    refine ⟨μ, ?_, hμ⟩
    intro hμ0
    exact hne (by rw [hμ, hμ0, zero_smul])
  · rintro ⟨c, hc0, hc⟩
    rw [hc, uCitedRoot_smul h hvv hc0]

theorem uCited_normalizer_root_zero (h : UnitaryFieldData p f K) (hr : 2 ≤ r) (hε : ε ≤ 1) :
    Subgroup.normalizer (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K)) :
        Set ↥(hypSU h r ε)) =
      isoStabilizer h r ε (hypFlag h r ε 1) := by
  set e0 : HypIndex r ε → K := Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) with he0def
  have hflag : hypFlag h r ε 1 = K ∙ e0 := by
    rw [hypFlag_eq_posFlag h hε (by omega), posFlag_one (by omega)]
  ext g
  rw [uCited_mem_normalizer_root_iff, mem_isoStabilizer, hflag]
  constructor
  · rintro ⟨c, hc0, hc⟩
    rw [Subgroup.smul_def, smul_eq_map, Submodule.map_span, Set.image_singleton,
      Matrix.mulVecLin_apply, hc]
    exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc0) e0
  · intro hg
    have h1 : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ e0 ∈
        (K ∙ e0).map (Matrix.mulVecLin
          (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K))) :=
      Submodule.mem_map.mpr ⟨e0, Submodule.mem_span_singleton_self e0, by
        rw [Matrix.mulVecLin_apply]⟩
    have h2 : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ e0 ∈
        g • (K ∙ e0) := by
      simpa only [Subgroup.smul_def, smul_eq_map] using h1
    rw [hg] at h2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h2
    refine ⟨c, ?_, hc.symm⟩
    intro hc0
    have hinj : Function.Injective (Matrix.mulVec
        ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)) :=
      Matrix.mulVec_injective_of_isUnit (Units.isUnit (g : GL (HypIndex r ε) K))
    have hzero : ((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *ᵥ
        e0 = 0 := by
      rw [← hc, hc0, zero_smul]
    have he0zero : e0 = 0 := hinj (by rw [hzero, Matrix.mulVec_zero])
    have hone : (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K) :
        HypIndex r ε → K) ≠ 0 := by
      intro hzero'
      have := congrFun hzero' (Sum.inl (⟨0, by omega⟩ : Fin r))
      simpa using this
    rw [he0def] at he0zero
    exact hone he0zero

theorem uCited_conj_root_zero (h : UnitaryFieldData p f K) (hr : 2 ≤ r) {c : K}
    (hc : c ∈ h.traceZero) (hc0 : c ≠ 0) :
    (uCitedRoot h r ε (Pi.single (Sum.inl (⟨0, by omega⟩ : Fin r)) (1 : K))).map
        (MulAut.conj (uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc)).toMonoidHom =
      uCitedRoot h r ε (Pi.single (Sum.inl (⟨1, by omega⟩ : Fin r)) (1 : K)) := by
  rw [map_conj_uCitedRoot h (uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc)
    (hypForm_single_inl_self h (⟨0, by omega⟩ : Fin r))]
  have hLP := isLinePerm_uWeylRep (h := h) (ε := ε) (c := c) hc hc0
    (⟨0, by omega⟩ : Fin r)
  have hσ : weylPerm (ε := ε) (simpleRefl r (⟨0, by omega⟩ : Fin r))
      (Sum.inl (⟨0, by omega⟩ : Fin r)) = Sum.inl (⟨1, by omega⟩ : Fin r) := by
    rw [weylPerm_inl, simpleRefl_inl]
    unfold simpleSnd
    rw [dif_pos (by omega : (0 : ℕ) + 1 < r)]
    simp [lineCoord]
  have hmul := monomial_mulVec_single hLP (Sum.inl (⟨0, by omega⟩ : Fin r))
  rw [hσ] at hmul
  have hcne : (((uWeylRep ε h (⟨0, by omega⟩ : Fin r) c hc : hypSU h r ε) :
      GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K)
      (Sum.inl (⟨1, by omega⟩ : Fin r)) (Sum.inl (⟨0, by omega⟩ : Fin r)) ≠ 0 := by
    have h := hLP.apply_ne_zero (Sum.inl (⟨0, by omega⟩ : Fin r))
    rwa [hσ] at h
  rw [hmul]
  exact uCitedRoot_smul h (hypForm_single_inl_self h (⟨1, by omega⟩ : Fin r)) hcne

end CFSG.LocalAnalysis.WeakClosure81

end

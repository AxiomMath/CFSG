module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLExcFrame

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def CensusCasesVx (R : RawFrameData) (vx : R.V) : Prop :=
  vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ → R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∉ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
    (∃ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} ∧ ∃ k, Candidate R vx j z k ∧
        CommonWitness R vx z ℓ k) ∨
    (∃ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} ∧ ∃ k, Candidate R vx j z k ∧
        z ∉ R.inside k ∧ TwoNodeLabels 3 (R.label k) (R.label j)) ∨
    TwoNodeLabels 3 (R.label ℓ) (R.label j) ∨
    (∀ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} → ∀ k, Candidate R vx j z k →
        R.inside j ≤ R.inside k →
        TwoNodeLabels 3 (R.label k) (R.label j) ∨ AmbientWitness R vx z ℓ k)

theorem censusCases_iff_forall (R : RawFrameData) : CensusCases R ↔ ∀ vx, CensusCasesVx R vx :=
  Iff.rfl

@[expose] def InLCommonCasesVx (R : RawFrameData) (vx : R.V) : Prop :=
  vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ →
    (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ)) →
    R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∈ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
  ∃ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} ∧ ∃ k : R.Code, Candidate R vx j z k ∧
    CommonWitness R vx z ℓ k

theorem inLCommonCases_iff_forall (R : RawFrameData) :
    InLCommonCases R ↔ ∀ vx, InLCommonCasesVx R vx :=
  Iff.rfl

namespace FrameAut

variable {R : RawFrameData} (A : FrameAut R)

theorem commonWitness (vx z : R.V) (ℓ k : R.Code) (h : CommonWitness R vx z ℓ k) :
    CommonWitness R (A.g vx) (A.g z) (A.σ ℓ) (A.σ k) := by
  obtain ⟨W, hL, hK, hx, hz⟩ := h
  refine ⟨W.map A.g, ?_, ?_, W.map_ker A.g _ hx, W.map_ker A.g _ hz⟩
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hL
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hK

theorem ambientWitness (vx z : R.V) (ℓ k : R.Code) (h : AmbientWitness R vx z ℓ k) :
    AmbientWitness R (A.g vx) (A.g z) (A.σ ℓ) (A.σ k) := by
  obtain ⟨W, hL, ha, hx, hz, hB, rest⟩ := h
  refine ⟨W.map A.g, ?_, ?_, W.map_ker A.g _ hx, fun i hia hib => ?_, W.map_basis A.g hB, rest⟩
  · rw [A.normalizerGroup_eq]
    exact W.map_parab_eq A.g hL
  · rw [A.normalizerGroup_sup]
    exact W.map_simpleRefl_mem A.g ha
  · rw [W.map_root_apply A.g i z]
    exact hz i hia hib

theorem exists_map_eq (U' : Submodule (ZMod 3) R.V) :
    ∃ U : Submodule (ZMod 3) R.V, U' = U.map (A.g : R.V →ₗ[ZMod 3] R.V) :=
  ⟨U'.map (A.g.symm : R.V →ₗ[ZMod 3] R.V), ((Submodule.map_symm_eq_iff A.g).mp rfl).symm⟩

theorem censusCasesVx_map {vx : R.V} (h : CensusCasesVx R vx) : CensusCasesVx R (A.g vx) := by
  intro hvx ℓ' hℓ hocc hcent hins U' hU hxU j' hj hjocc hjcent hjins hjN
  obtain ⟨ℓ, rfl⟩ := A.σ.surjective ℓ'
  obtain ⟨j, rfl⟩ := A.σ.surjective j'
  obtain ⟨U, rfl⟩ := A.exists_map_eq U'
  rw [A.admissible_iff] at hℓ hj
  rw [A.occurs_span_iff] at hocc
  rw [A.cent_eq_span_iff] at hcent
  rw [A.inside_eq, A.mem_map_iff] at hins
  rw [LinearEquiv.finrank_map_eq] at hU
  rw [A.mem_map_iff] at hxU
  rw [A.occurs_iff] at hjocc
  rw [A.cent_eq, A.map_eq_map_iff] at hjcent
  rw [A.inside_le_iff] at hjins
  rw [A.normalizerGroup_le_iff] at hjN
  rcases h (fun h0 => hvx (by rw [h0, map_zero])) ℓ hℓ hocc hcent hins U hU hxU j hj hjocc
    hjcent hjins hjN with ⟨z, hzU, hzx, k, hk, hW⟩ | ⟨z, hzU, hzx, k, hk, hzk, h2⟩ | h3 | h4
  · refine Or.inl ⟨A.g z, (A.mem_map_iff z U).mpr hzU, (A.mem_span_iff z vx).not.mpr hzx, A.σ k,
      (A.candidate_iff vx z j k).mpr hk, A.commonWitness _ _ _ _ hW⟩
  · refine Or.inr (Or.inl ⟨A.g z, (A.mem_map_iff z U).mpr hzU, (A.mem_span_iff z vx).not.mpr hzx,
      A.σ k, (A.candidate_iff vx z j k).mpr hk, ?_, by rwa [A.label_eq, A.label_eq]⟩)
    rw [A.inside_eq, A.mem_map_iff]
    exact hzk
  · exact Or.inr (Or.inr (Or.inl (by rwa [A.label_eq, A.label_eq])))
  · refine Or.inr (Or.inr (Or.inr fun z' hzU z'x k' hk hkins => ?_))
    obtain ⟨k, rfl⟩ := A.σ.surjective k'
    obtain ⟨z, rfl⟩ := A.g.surjective z'
    rw [A.mem_map_iff] at hzU
    rw [A.mem_span_iff] at z'x
    rw [A.candidate_iff] at hk
    rw [A.inside_le_iff] at hkins
    rcases h4 z hzU z'x k hk hkins with h5 | h6
    · exact Or.inl (by rwa [A.label_eq, A.label_eq])
    · exact Or.inr (A.ambientWitness _ _ _ _ h6)

theorem inLCommonCasesVx_map {vx : R.V} (h : InLCommonCasesVx R vx) :
    InLCommonCasesVx R (A.g vx) := by
  intro hvx ℓ' hℓ hlab hocc hcent hins U' hU hxU j' hj hjocc hjcent hjins hjN
  obtain ⟨ℓ, rfl⟩ := A.σ.surjective ℓ'
  obtain ⟨j, rfl⟩ := A.σ.surjective j'
  obtain ⟨U, rfl⟩ := A.exists_map_eq U'
  rw [A.label_eq] at hlab
  rw [A.admissible_iff] at hℓ hj
  rw [A.occurs_span_iff] at hocc
  rw [A.cent_eq_span_iff] at hcent
  rw [A.inside_eq, A.mem_map_iff] at hins
  rw [LinearEquiv.finrank_map_eq] at hU
  rw [A.mem_map_iff] at hxU
  rw [A.occurs_iff] at hjocc
  rw [A.cent_eq, A.map_eq_map_iff] at hjcent
  rw [A.inside_le_iff] at hjins
  rw [A.normalizerGroup_le_iff] at hjN
  obtain ⟨z, hzU, hzx, k, hk, hW⟩ := h (fun h0 => hvx (by rw [h0, map_zero])) ℓ hℓ hlab hocc
    hcent hins U hU hxU j hj hjocc hjcent hjins hjN
  exact ⟨A.g z, (A.mem_map_iff z U).mpr hzU, (A.mem_span_iff z vx).not.mpr hzx, A.σ k,
    (A.candidate_iff vx z j k).mpr hk, A.commonWitness _ _ _ _ hW⟩

end FrameAut

end CFSG.StandardType.GGQ2Frame

end

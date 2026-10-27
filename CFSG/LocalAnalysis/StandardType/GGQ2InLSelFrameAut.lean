module

public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameAut
public import CFSG.LocalAnalysis.StandardType.GGQ2InLLeafSel

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def InLSelVx (R : RawFrameData) (P : R.Code → R.Code → Prop) (vx : R.V) : Prop :=
  vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ →
    (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ)) →
    R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∈ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
  ∀ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} → ∀ k : R.Code, Candidate R vx j z k →
    R.inside j ≤ R.inside k → InLLeafAt R vx z ℓ k ∨ P j k

theorem inLLeafOrSelCases_of_inLSelVx {R : RawFrameData} {P : R.Code → R.Code → Prop}
    (hP : ∀ j k, P j k → InLSelD6Raw R j k ∨ InLSelDetRaw R k) (h : ∀ vx, InLSelVx R P vx) :
    InLLeafOrSelCases R :=
  fun vx hvx ℓ hℓ hq hocc hcent hin U hU hxU j hj hjocc hjcent hjins hjN z hz hzx k hk hjk =>
    (h vx hvx ℓ hℓ hq hocc hcent hin U hU hxU j hj hjocc hjcent hjins hjN z hz hzx k hk
      hjk).imp_right (hP j k)

namespace FrameAut

variable {R : RawFrameData} (A : FrameAut R)

theorem inLSelVx_map {P : R.Code → R.Code → Prop} (hP : ∀ j k, P j k → P (A.σ j) (A.σ k))
    {vx : R.V} (h : InLSelVx R P vx) : InLSelVx R P (A.g vx) := by
  intro hvx ℓ' hℓ hlab hocc hcent hins U' hU hxU j' hj hjocc hjcent hjins hjN z' hzU z'x k' hk
    hkins
  obtain ⟨ℓ, rfl⟩ := A.σ.surjective ℓ'
  obtain ⟨j, rfl⟩ := A.σ.surjective j'
  obtain ⟨U, rfl⟩ := A.exists_map_eq U'
  obtain ⟨k, rfl⟩ := A.σ.surjective k'
  obtain ⟨z, rfl⟩ := A.g.surjective z'
  rw [A.label_eq] at hlab
  rw [A.admissible_iff] at hℓ hj
  rw [A.occurs_span_iff] at hocc
  rw [A.cent_eq_span_iff] at hcent
  rw [A.inside_eq, A.mem_map_iff] at hins
  rw [LinearEquiv.finrank_map_eq] at hU
  rw [A.mem_map_iff] at hxU hzU
  rw [A.occurs_iff] at hjocc
  rw [A.cent_eq, A.map_eq_map_iff] at hjcent
  rw [A.inside_le_iff] at hjins hkins
  rw [A.normalizerGroup_le_iff] at hjN
  rw [A.mem_span_iff] at z'x
  rw [A.candidate_iff] at hk
  rcases h (fun h0 => hvx (by rw [h0, map_zero])) ℓ hℓ hlab hocc hcent hins U hU hxU j hj hjocc
    hjcent hjins hjN z hzU z'x k hk hkins with h1 | h2
  · exact Or.inl (A.inLLeafAt _ _ _ _ h1)
  · exact Or.inr (hP j k h2)

end FrameAut

end CFSG.StandardType.GGQ2Frame

end

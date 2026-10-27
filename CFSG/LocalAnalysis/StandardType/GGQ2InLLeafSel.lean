module

public import CFSG.LocalAnalysis.StandardType.GGQ2InLCoverFrame

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

@[expose] def InLSelDetRaw (R : RawFrameData) (k : R.Code) : Prop :=
  ∃ e : Fin 6 → R.Root, (∀ i i', R.pairing (e i) (e i') = CartanMatrix.E 6 i i') ∧
    R.normalizerGroup k = Subgroup.closure (R.reflection '' Set.range e)

@[expose] def InLSelD6Raw (R : RawFrameData) (j k : R.Code) : Prop :=
  ∃ (e : Fin 6 → R.Root) (ε : Fin 6 → ℤˣ) (b : Fin 6), (b = 4 ∨ b = 5) ∧
    (∀ i i', ((ε i : ℤ) * ε i') * R.pairing (e i) (e i') = CartanMatrix.D 6 i i') ∧
    R.normalizerGroup k = Subgroup.closure (R.reflection '' Set.range e) ∧
    R.normalizerGroup j = Subgroup.closure (R.reflection '' (e '' {i | i ≠ b}))

@[expose] def InLLeafOrSelCases (R : RawFrameData) : Prop :=
  ∀ vx : R.V, vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ → (∃ lab : LargeEvenLabel, GGLabQTwo 3 lab ∧ GGLabelIso lab (R.label ℓ)) →
    R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∈ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
  ∀ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} → ∀ k : R.Code, Candidate R vx j z k →
    R.inside j ≤ R.inside k → InLLeafAt R vx z ℓ k ∨ InLSelD6Raw R j k ∨ InLSelDetRaw R k

end CFSG.StandardType.GGQ2Frame

end

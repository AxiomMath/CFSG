module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08Core
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabGlueAll
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigHSmall
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigCardAut
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXDetDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

structure GGQ2S08BigLin {ℓ : ℕ} (s : Fin ℓ → (Vn (ℓ + 1) ≃ₗ[ZMod 3] Vn (ℓ + 1)))
    (Mx : CoxeterMatrix (Fin ℓ)) (xv : Vn (ℓ + 1)) (H : Submodule (ZMod 3) (Vn (ℓ + 1))) :
    Prop where
  hx : xv ≠ 0
  hH : IsCompl H (Submodule.span (ZMod 3) {xv})
  hM : Mx = CoxeterMatrix.A ℓ ∨ Mx = CoxeterMatrix.B ℓ ∨ Mx = ggCoxeterMatrixD ℓ
  srefl : ∀ i, GGLinRefl (s i)
  sH : ∀ i, ∃ h ∈ H, h ≠ 0 ∧ ∀ v, s i v - v ∈ Submodule.span (ZMod 3) {h}
  rel : ∀ i j, i ≠ j → (s i * s j) ^ Mx i j = 1
  dist : ∀ i j, i ≠ j → s i ≠ s j
  ncomm : ∀ i j, i ≠ j → Mx i j ≠ 2 → s i * s j ≠ s j * s i
  Wfix : ∀ v, (∀ w ∈ Subgroup.closure (Set.range s), w v = v) ↔
    v ∈ Submodule.span (ZMod 3) {xv}
  WH : ∀ w ∈ Subgroup.closure (Set.range s), ∀ h ∈ H, w h ∈ H
  WirrH : ∀ U : Submodule (ZMod 3) (Vn (ℓ + 1)), U ≤ H →
    (∀ w ∈ Subgroup.closure (Set.range s), ∀ u ∈ U, w u ∈ U) → U = ⊥ ∨ U = H

end CFSG.StandardType

end

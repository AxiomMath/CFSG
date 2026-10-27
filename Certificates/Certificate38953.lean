module

public import CFSG.GF2Type.Widths1112.Co2FormDefs
import Certificates.Kernel.Co2W11.Glue

public section

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2 CFSG.GF2W1112

public section

namespace Certificates

open CFSG.GF2Type.Widths1112 CertificateChecks.KernelCo2W11

open CFSG.GF2Type.Widths1112 CFSG.Sporadic.SmallF2 CFSG.GF2W1112 in
theorem certificate38953 : (∀ Y : Submodule (ZMod 2) Vec22, toVecD 22 (w12Co2Rep 0) ∈ Y →
      (∀ y ∈ Y, bil₀₂ y (toVecD 22 (w12Co2Rep 0)) = 0) →
      (∀ g : CFSG.Blueprint.NativeSporadic.Co2,
        co2Act g (toVecD 22 (w12Co2Rep 0)) = toVecD 22 (w12Co2Rep 0) →
          ∀ y ∈ Y, co2Act g y ∈ Y) →
      Y = Submodule.span (ZMod 2) {toVecD 22 (w12Co2Rep 0)} ∨
        ∀ y, bil₀₂ y (toVecD 22 (w12Co2Rep 0)) = 0 → y ∈ Y) ∧
    ∃ a b : Vec22, bil₀₂ a (toVecD 22 (w12Co2Rep 0)) = 0 ∧
      bil₀₂ b (toVecD 22 (w12Co2Rep 0)) = 0 ∧ bil₀₂ a b = 1 := by
  have he : bil₀₂ (CFSG.Sporadic.SmallF2.toVecD 22 S0.spinE) (CFSG.Sporadic.SmallF2.toVecD 22 40)
      = 1 := by
    rw [bil₀₂_toVecD, s0_spinE]
    rfl
  have h1 : bil₀₂ (CFSG.Sporadic.SmallF2.toVecD 22 1) (CFSG.Sporadic.SmallF2.toVecD 22 40) = 0 := by
    rw [bil₀₂_toVecD, pair_1]
    rfl
  have h2 : bil₀₂ (CFSG.Sporadic.SmallF2.toVecD 22 128) (CFSG.Sporadic.SmallF2.toVecD 22 40)
      = 0 := by
    rw [bil₀₂_toVecD, pair_128]
    rfl
  have h3 : bil₀₂ (CFSG.Sporadic.SmallF2.toVecD 22 1) (CFSG.Sporadic.SmallF2.toVecD 22 128)
      = 1 := by
    rw [bil₀₂_toVecD, pair_1_128]
    rfl
  exact ⟨fun Y hrY hperp hinv => irr_rep0 s0_ts (f0_row _ _ s0_F0) he Y hrY hperp hinv,
    CFSG.Sporadic.SmallF2.toVecD 22 1, CFSG.Sporadic.SmallF2.toVecD 22 128, h1, h2, h3⟩

end Certificates

end

end

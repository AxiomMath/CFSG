module

import CFSG.LieType.Universal.Spin.Generation.Eichler
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalCoreO2
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalSettingW

public section

namespace CFSG.StandardType.LieKnownR2.POmega.NC

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

theorem spinMinus_fpf {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hβ : β ∈ (Spin.Twisted.minusDatum n hirr).roots)
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c))) :
    ∃ h : ↥(spinGroup (Spin.quadMinus n F b c)),
      Odd (orderOf h) ∧
      h ∈ Subgroup.normalizer
        (((((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) :
          Subgroup ↥(spinGroup (Spin.quadMinus n F b c))) :
            Set ↥(spinGroup (Spin.quadMinus n F b c))) ∧
      ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) :
          Subgroup ↥(spinGroup (Spin.quadMinus n F b c))) :
            Set ↥(spinGroup (Spin.quadMinus n F b c)))),
        h * y = y * h → y ∈ (((Spin.Twisted.minusDatum n hirr).rootGroup β).map
          (MulAut.conj u).toMonoidHom) := by
  have hS : Radical.SpinOmegaData (Spin.quadMinus n F b c) :=
    Radical.spinOmegaData_quadMinus hn hirr
  obtain ⟨P, P', hOrth, hR, hW⟩ := Radical.exists_frame_hW_of_root_minus hn hirr hS hβ hl u
  obtain ⟨h, hh, horder, hnorm⟩ := Radical.exists_spin_lift_orthSiegelLevi hS hOrth
  have hV : 6 ≤ Module.finrank F (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
    omega
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [horder]; norm_num
  · rw [hR]
    exact hnorm
  · intro y hy hcomm
    rw [hR] at hy ⊢
    exact Radical.orthSiegelCore_centralizer_levi_le_siegelRoot hS hOrth hV hh
      (Radical.siegelO2_le_orthSiegelCore hS hOrth hV hW hy) hcomm

end CFSG.StandardType.LieKnownR2.POmega.NC

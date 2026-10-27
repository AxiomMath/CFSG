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

theorem spinPlus_fpf {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum n F (by omega)).roots)
    (u : ↥(spinGroup (Spin.quadPlus n F))) :
    ∃ h : ↥(spinGroup (Spin.quadPlus n F)),
      Odd (orderOf h) ∧
      h ∈ Subgroup.normalizer
        (((((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) :
          Subgroup ↥(spinGroup (Spin.quadPlus n F))) : Set ↥(spinGroup (Spin.quadPlus n F))) ∧
      ∀ y ∈ pCoreOf 2 (Subgroup.normalizer
        (((((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) :
          Subgroup ↥(spinGroup (Spin.quadPlus n F))) : Set ↥(spinGroup (Spin.quadPlus n F)))),
        h * y = y * h → y ∈ (((Spin.plusDatum n F (by omega)).rootGroup β).map
          (MulAut.conj u).toMonoidHom) := by
  have hS : Radical.SpinOmegaData (Spin.quadPlus n F) := Radical.spinOmegaData_quadPlus (by omega)
  obtain ⟨P, P', hOrth, hR, hW⟩ := Radical.exists_frame_hW_of_root_plus hn hS hβ u
  obtain ⟨h, hh, horder, hnorm⟩ := Radical.exists_spin_lift_orthSiegelLevi hS hOrth
  have hV : 6 ≤ Module.finrank F (Fin n ⊕ Fin n → F) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
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

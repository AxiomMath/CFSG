module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownForms
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Filtration
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2FixedPointOdd
import CFSG.LieType.Universal.Spin.Generation.Eichler
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaNCPlus
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaNCMinus
public import CFSG.ClassicalInvolution.ModelFacts.CentralLift

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem
open scoped commutatorElement

namespace CFSG.StandardType.LieKnownR2.POmega

theorem ggRootNoCentral_spinPlus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum n F (by omega)).roots) (u : ↥(spinGroup (Spin.quadPlus n F))) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(spinGroup (Spin.quadPlus n F)))
      (((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : Finite ↥(spinGroup (Spin.quadPlus n F)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker (Spin.quadPlus n F)
      (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  obtain ⟨h, hodd, hhN, hfix⟩ := NC.spinPlus_fpf hn hβ u
  exact noCentral_of_fixedPoint_odd hodd ⟨Subgroup.mem_top _, hhN⟩ (by
    intro y hy hcomm
    exact hfix y (by simpa only [top_inf_eq] using hy) hcomm)

theorem ggRootNoCentral_spinMinus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hβ : β ∈ (Spin.Twisted.minusDatum n hirr).roots)
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c))) :
    GGRootNoCentralAt (⊤ : Subgroup ↥(spinGroup (Spin.quadMinus n F b c)))
      (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  haveI : Finite ↥(spinGroup (Spin.quadMinus n F b c)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker (Spin.quadMinus n F b c)
      (coe_ker_spinMatrix_quadMinus (n := n) (K := F) hirr)
  obtain ⟨h, hodd, hhN, hfix⟩ := NC.spinMinus_fpf hn hirr hβ hl u
  exact noCentral_of_fixedPoint_odd hodd ⟨Subgroup.mem_top _, hhN⟩ (by
    intro y hy hcomm
    exact hfix y (by simpa only [top_inf_eq] using hy) hcomm)

end CFSG.StandardType.LieKnownR2.POmega

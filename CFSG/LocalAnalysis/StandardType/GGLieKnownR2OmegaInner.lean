module

public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.Spin.Datum
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutMain
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaD4Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerTransport
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaInnerMatrix

public section

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped commutatorElement

namespace CFSG.StandardType.LieKnownR2.POmega

theorem ggRootNormInner_spinPlus_ge_five {n : ℕ} (hn : 5 ≤ n) {F : Type} [Field F] [Finite F]
    [CharP F 2] {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum n F (by omega)).roots) (u : ↥(spinGroup (Spin.quadPlus n F))) :
    GGRootNormInner
      (((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
  Inner.ggRootNormInner_of_semilinear_similitude_plus hn hβ u
    (fun A φ μ hsim y hy2 htriv hmat =>
      Inner.ggRootNormInner_semilinear_plus (by omega) hβ u A φ μ hsim y hy2 htriv hmat)

theorem ggRootNormInner_spinPlus
    {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {β : Fin (Spin.plusDatum n F (by omega)).rank → ℤ}
    (hβ : β ∈ (Spin.plusDatum n F (by omega)).roots) (u : ↥(spinGroup (Spin.quadPlus n F))) :
    GGRootNormInner
      (((Spin.plusDatum n F (by omega)).rootGroup β).map (MulAut.conj u).toMonoidHom) := by
  rcases Nat.eq_or_lt_of_le hn with rfl | hn5
  · exact ggRootNormInner_spinPlus_four (F := F) (β := β) hβ u
  · exact ggRootNormInner_spinPlus_ge_five (by omega) hβ u

theorem ggRootNormInner_spinMinus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {β : Fin (Spin.Twisted.minusDatum n hirr).rank → ℤ}
    (hβ : β ∈ (Spin.Twisted.minusDatum n hirr).roots)
    (hl : GGLongRoot (Spin.Twisted.minusDatum n hirr) β)
    (u : ↥(spinGroup (Spin.quadMinus n F b c))) :
    GGRootNormInner
      (((Spin.Twisted.minusDatum n hirr).rootGroup β).map (MulAut.conj u).toMonoidHom) :=
  Inner.ggRootNormInner_of_semilinear_similitude_minus hn hirr hβ hl u
    (fun A φ μ hsim y hy2 htriv hmat =>
      Inner.ggRootNormInner_semilinear_minus hn hirr hβ hl u A φ μ hsim y hy2 htriv hmat)

end CFSG.StandardType.LieKnownR2.POmega

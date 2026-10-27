module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22OuterInputs
import Certificates.Kernel.LocalQT.Outer.C4136

public section

namespace Certificates

open CFSG.KD.LQT.C4136 CFSG.KC.LQT.W CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier
  CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu in
theorem certificate4136 : (m22outerOK m22OutRep1 (m22OuterK.getD 0 ([], [])) = true ∧
            m22outerOK m22OutRep2 (m22OuterK.getD 1 ([], [])) = true) := by
  refine ⟨?_, ?_⟩ <;> unfold m22outerOK
  · exact outer_sound [m22gA, m22gB] m22OutRep1 (m22OuterK.getD 0 ([], [])) hG hr₁ k₁
  · exact outer_sound [m22gA, m22gB] m22OutRep2 (m22OuterK.getD 1 ([], [])) hG hr₂ k₂

end Certificates

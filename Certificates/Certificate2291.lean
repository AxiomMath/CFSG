module

public import CFSG.Sporadic.SuzOddCore.CTIBase
public import CFSG.Sporadic.SuzOddCore.ThreeLocalA
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourGroupSpec
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public meta import CFSG.Sporadic.SuzOddCore.CTICheck
public import Certificates.Certificate2289
public import Certificates.Certificate2293
public import Certificates.Certificate2296
public import Certificates.Certificate2306
public meta import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.LocalVocabulary
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.SuzOddCore.CompQuot
public import CFSG.Sporadic.SuzOddCore.CompQuot
public import CFSG.Sporadic.SuzOddCore.GammaBound
public import CFSG.Sporadic.SuzOddCore.GraphData
public meta import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds
public import CFSG.Sporadic.SuzOddCore.InvCentralizerBounds

public section

open CFSG.Sporadic.SuzOddCore

namespace Certificates

open CFSG CFSG.Sporadic CFSG.Sporadic.SuzOddCore CFSG.Certificates CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four in
open scoped commutatorElement in
theorem certificate2291 : ∀ U : Finset (Fin 10), 0 ∈ U →
    (∑ l ∈ U, classSizes.getD l 0) ∣ 20160 → U = {0} ∨ U = Finset.univ :=
  by decide +kernel

end Certificates

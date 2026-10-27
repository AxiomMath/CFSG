
module

public import CFSG.Sporadic.ThSchreier.CoreHyperplaneBase

public import CFSG.Sporadic.ThSchreier.NoTransvectionBase1
public import CFSG.Sporadic.ThSchreier.Max3AutBase1
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.CoreBase1
public import CFSG.Sporadic.Th.Max3.AltNine
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Sporadic.Th.Max3.QuotientInputs
public import CFSG.Sporadic.Th.Max3.Data
public import CFSG.Sporadic.ThSchreier.NoTransvectionInputs
public meta import CFSG.Sporadic.ThSchreier.Rigidity

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates Matrix

theorem nf_eq_mul
    (s : ZMod 2) (v : Fin 8 → ZMod 2) : nf s v = z ^ s.val * nf 0 v := by
  simp only [nf, ZMod.val_zero, pow_zero, one_mul]

end CFSG.Sporadic.ThSchreier

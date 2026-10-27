module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenAlternating

public section

namespace CFSG.StandardType

inductive GGResLineJType where
  | A2 | B2 | A3 | B3 | C3
  deriving DecidableEq

@[expose] def GGResLineJType.rank : GGResLineJType → ℕ
  | .A2 | .B2 => 2
  | .A3 | .B3 | .C3 => 3

@[expose] def GGResLineJType.cartan : (T : GGResLineJType) → Matrix (Fin T.rank) (Fin T.rank) ℤ
  | .A2 => CartanMatrix.A 2
  | .B2 => CartanMatrix.B 2
  | .A3 => CartanMatrix.A 3
  | .B3 => CartanMatrix.B 3
  | .C3 => CartanMatrix.C 3

@[expose] def GGResLineJType.bad : GGResLineJType → ℕ
  | .A2 | .B2 => 9
  | .A3 => 27
  | .B3 | .C3 => 5

end CFSG.StandardType

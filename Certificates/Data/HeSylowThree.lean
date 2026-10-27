module

public import Certificates.Data.B3Spor3.He
public meta import Certificates.Data.B3Spor3.He

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3S3

set_option compiler.extract_closed false

@[expose] def heS3QNonabOK (_ : Unit := ()) : Bool :=
  let Q := heS3QGens
  decide (2 ≤ Q.size) && (Q[0]!)[(Q[1]!)[0]!]! != (Q[1]!)[(Q[0]!)[0]!]!

end CFSG.HardMathSupport.Solomon.Coordinator.B3S3

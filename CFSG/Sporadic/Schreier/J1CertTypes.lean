module

public import CFSG.Monster.B.Mathieu.CertData

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu

structure J1CertificateFile where
  schemaVersion : ℕ
  group : String
  prime : ℕ
  dimension : ℕ
  vectors : List (List ℕ)
  basisIndices : List ℕ
  chain : ChainRecord
  sylows : List SylowRecord
  deriving DecidableEq, Inhabited

end CFSG.Sporadic.Schreier

end

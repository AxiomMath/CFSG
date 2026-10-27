module

public import CFSG.Monster.B.Mathieu.CertData

public section

namespace CFSG.Sporadic.Co2Cert

open CFSG.Monster.B.Mathieu

structure Co2Merge where
  representative : ℕ
  instructions : List (List ℕ)
  deriving DecidableEq, Inhabited

structure Co2CertFile where
  schemaVersion : ℕ
  group : String
  prime : ℕ
  dimension : ℕ
  vectors : List (List ℕ)
  basisIndices : List ℕ
  chain : ChainRecord
  coprimeConjugator : List ℤ
  coprimeChain : ChainRecord
  point : ℕ
  stabilizerGeneratorIndices : List ℕ
  stabilizerOrbits : List (List ℕ)
  merges : List Co2Merge
  deriving DecidableEq, Inhabited

end CFSG.Sporadic.Co2Cert

end

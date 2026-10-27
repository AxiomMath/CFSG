module

public import CFSG.Sporadic.Schreier.J1CertData
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Sporadic.Schreier.J1CertData
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Monster.B.Mathieu CFSG.Monster.B.Binary.Native

@[expose] def j1CertificateSha : ℕ :=
  0x9f8fe6e4bbf9891f9b90f53d73d86fb00a1e9bcae1a119081c79e4f8b6f35289

@[expose] def J1CertificateFile.shapeOK (f : J1CertificateFile) : Bool :=
  f.schemaVersion == 1 && f.group == "J1" && f.prime == 11 && f.dimension == 7 &&
    f.vectors.length == 3080 && f.vectors.all (fun v => v.length == 7 && v.all (· ≤ 10)) &&
    f.basisIndices == [0, 1, 2, 3, 4, 5, 6] && f.chain.degree == 3080 &&
    f.chain.generators.length == 2 &&
    (f.chain.generators ++ f.chain.strongGenerators).all (isPermList 3080) &&
    f.sylows.map (·.prime) == [2, 3, 5, 7, 11, 19] &&
    f.sylows.all fun s => s.generators.all (isPermList 3080) &&
      s.normalGeneration.all fun ng => isPermList 3080 ng.representative && ng.chain.degree == 3080

end CFSG.Sporadic.Schreier

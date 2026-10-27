module

public import CFSG.Sporadic.Co2Cert.Data
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.Sporadic.Co2Cert.Data
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.Sporadic.Co2Cert

open CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2.Native CFSG.Monster.B.Binary.Native

@[expose] def co2CertSha : ℕ :=
  0x34a73ee35c6cc5bd2931dad1ca89dec81ca97a3807c1b53253ea0c283238b0a2

@[expose] def co2Keys : List String :=
  ["basis_indices", "chain", "coprime_chain", "coprime_conjugator", "dimension", "group",
    "merges", "point", "prime", "schema_version", "stabilizer_generator_indices",
    "stabilizer_orbits", "vectors"]

@[expose] def co2BasisList : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 23, 28, 41, 61]

@[expose] def isPermList (n : ℕ) (l : List ℕ) : Bool :=
  l.length == n && isInvA n l.toArray (invCand n l.toArray)

@[expose] def chainShapeOK (c : ChainRecord) (n k r : ℕ) (base : List ℕ) : Bool :=
  c.degree == n && c.generators.length == k && c.strongGenerators.length == r &&
    c.derivations.length == r - k && c.generators.all (isPermList n) &&
    c.strongGenerators.all (isPermList n) && c.base == base &&
    (List.range (r - k)).all fun j => lettersOK (j + k) (c.derivations.getD j [])

@[expose] def increasingBelow (n : ℕ) (l : List ℕ) : Bool :=
  l.all (· < n) && (List.range (l.length - 1)).all fun k => l.getD k 0 < l.getD (k + 1) 0

@[expose] def tripleOK (t : List ℕ) : Bool :=
  t.length == 3 && t.getD 0 0 < 2 && t.getD 1 0 < 2300 && t.getD 2 0 < 2300

@[expose] def co2ShapeOK : Bool :=
  let r := co2Rec
  r.schemaVersion == 1 && r.group == "Co2" && r.prime == 2 && r.dimension == 22 &&
    r.vectors.length == 2300 && r.vectors.all (fun v => v.length == 22 && v.all (· < 2)) &&
    r.basisIndices == co2BasisList &&
    chainShapeOK r.chain 2300 2 11 [0, 1, 2, 3, 5, 4] &&
    chainShapeOK r.coprimeChain 2300 2 17 [0, 1, 3, 2, 5, 4] &&
    r.coprimeConjugator == [-1, 2, 2, 1, 2, -1] && r.point == 0 &&
    r.stabilizerGeneratorIndices == [0, 2, 3, 4, 5, 6, 7, 8, 9, 10] &&
    r.stabilizerOrbits.map List.length == [1, 1408, 891] &&
    r.stabilizerOrbits.all (increasingBelow 2300) &&
    r.merges.map (·.representative) == [1, 3] &&
    r.merges.map (·.instructions.length) == [2298, 2298] &&
    r.merges.all (fun m => m.instructions.all tripleOK)

end CFSG.Sporadic.Co2Cert

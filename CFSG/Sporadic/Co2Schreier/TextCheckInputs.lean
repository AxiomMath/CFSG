module

public import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.Check
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public meta import CFSG.Sporadic.Co2Schreier.Text
public meta import CFSG.Sporadic.Co2Cert.Check
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Binary.Native CFSG.Sporadic.Co2Cert

@[expose] def localSha : ℕ :=
  0x96c6dbf062ccf86eefc67923beb4f94f7de6e7ec3b360c1700e960730b5ee165

@[expose] def localKeyList : List String :=
  ["C_initial_center_word", "C_initial_words", "C_strong_derivations", "D_center_word",
    "D_strong_derivations", "D_words", "Frattini_profiles", "Q_words", "R_words",
    "S_quotient_words", "alignment_intermediate_word", "alignment_odd_orders", "chains",
    "expected_Frattini_rank", "expected_centralizer_indices", "schema_version", "z_R_word"]

@[expose] def localChainKeyList : List String := ["C", "D", "Q_action", "R_action", "S", "join"]

@[expose] def extWordsOK (k : ℕ) (ds : List (List ℤ)) : Bool :=
  (List.range ds.length).all fun j => lettersOK (k + j) (ds.getD j [])

@[expose] def localShapeOK (L : LocalCert) : Bool :=
  L.schemaVersion == 1 && L.alignmentOddOrders == [3, 3] && L.expectedFrattiniRank == 5 &&
    L.expectedCentralizerIndices == [56925, 1024650] &&
    L.cInitialWords.length == 2 && L.cInitialWords.all (lettersOK 2) &&
    L.dWords.length == 2 && L.dWords.all (lettersOK 2) &&
    L.dStrongDerivations.length == 5 && extWordsOK 2 L.dStrongDerivations &&
    L.rWords.length == 10 && L.rWords.all (lettersOK 7) &&
    lettersOK 2 L.cInitialCenterWord && lettersOK 2 L.dCenterWord && lettersOK 10 L.zRWord &&
    lettersOK 2 L.alignmentIntermediateWord &&
    L.cStrongDerivations.length == 7 && extWordsOK 2 L.cStrongDerivations &&
    L.qWords.length == 8 && L.qWords.all (lettersOK 9) &&
    L.sQuotientWords.length == 7 && L.sQuotientWords.all (lettersOK 9) &&
    L.frattiniProfiles.length == 32 && L.frattiniProfiles.all (·.length == 12) &&
    chainShapeOK L.chains.C 2300 2 14 [0, 1, 2, 3, 4, 5] &&
    chainShapeOK L.chains.D 2300 2 12 [1, 2, 0, 3] &&
    chainShapeOK L.chains.qAction 512 2 17 [1, 2, 3, 5, 4, 7, 8, 6] &&
    chainShapeOK L.chains.rAction 2048 2 11 [3, 1, 2, 5, 8, 7, 4] &&
    chainShapeOK L.chains.S 2300 15 23 [0, 1, 3] &&
    chainShapeOK L.chains.join 2300 4 17 [0, 1, 2, 3, 4, 5]

end CFSG.Sporadic.Co2Schreier

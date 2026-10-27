
module

public import CFSG.Sporadic.Co2Schreier.WitText
public import CFSG.Sporadic.Co2Schreier.TextCheckBase
public meta import CFSG.Sporadic.Co2Schreier.WitText
public meta import CFSG.Sporadic.Co2Schreier.TextCheckBase
public meta import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Binary.Native CFSG.Sporadic.Co2Cert

@[expose] def witSha : ℕ :=
  0x358352375c60559a1677b10a5845b04ef0e353d0420a14c205ee24a49d58007d

@[expose] def rows22OK (l : List ℕ) : Bool := l.length == 22 && l.all (· < 2 ^ 22)

@[expose] def witShapeOK (W : WitCert) : Bool :=
  let L := W.wLocal
  let F := W.fusion
  let T := W.third
  L.sixAnchor == 29 && L.sixBasisIndices == [516, 1588, 1809, 1630, 312, 1801] &&
    L.sixGramRows == [54, 21, 59, 52, 47, 29] &&
    L.sixRows.length == 2 && L.sixRows.all (fun r => r.length == 6 && r.all (· < 64)) &&
    chainShapeOK L.sixActionChain 63 2 12 [0, 1, 3, 7, 15, 31] &&
    L.qQuotientBasisIndices == [1, 2, 3, 4, 5, 6, 7, 8] &&
    L.qQuotientActionRows.length == 2 &&
    L.qQuotientActionRows.all (fun r => r.length == 8 && r.all (· < 256)) &&
    L.dStrongFixedBySIndices == [6, 7, 8] && L.dCandidateSurvivors == [[0, 0], [0, 9]] &&
    L.dAdditionalFixedWords.length == 1 && L.dAdditionalFixedWords.all (lettersOK 2) &&
    L.dInnerSurvivors == [[0, 0], [0, 9]] &&
    F.sylowOrder == 262144 && F.representatives.length == 3 &&
    F.representatives.map (·.sylowIndex) == [44, 527, 23] &&
    F.representatives.map (·.rankMinusIdentity) == [6, 8, 10] &&
    F.representatives.all (fun r => rows22OK r.matrixRows) &&
    F.rankCounts == [[6, 221], [8, 1034], [10, 4888]] && F.fusionBatches.length == 72 &&
    F.fusionBatches.all (fun b => decide (b.representative < 3) && lettersOK 2 b.conjugatingWord &&
      b.pairs.all fun p => p.length == 2 && p.getD 1 0 % 2 == 1) &&
    T.baseIndices.length == 13 && T.baseIndices.all (· < 2300) && decide T.baseIndices.Nodup &&
    T.strongDerivations.length == 28 && extWordsOK 2 T.strongDerivations &&
    T.fixedPoints.length == 52 && T.fixedBasis.length == 12 &&
    T.odd.sylowThreeGenerators.length == 2 && T.odd.sylowThreeGenerators.all rows22OK &&
    rows22OK T.odd.sylowFiveGenerator && T.odd.obstructions.length == 12 &&
    T.odd.obstructions.map (·.prime) == [3, 3, 3, 3, 3, 3, 3, 3, 5, 5, 5, 5] &&
    T.odd.obstructions.all (fun o => rows22OK o.element && rows22OK o.conjugator)

end CFSG.Sporadic.Co2Schreier

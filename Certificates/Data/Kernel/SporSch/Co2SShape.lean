module

public import Certificates.Data.Kernel.Spor.Co2Shape
public import CFSG.Sporadic.Co2Schreier.WitLit

public section

namespace CFSG.KS.Co2SShape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Co2Shape CFSG.Sporadic.Co2Schreier
  CFSG.Monster.B.Mathieu

@[expose] noncomputable def mapL {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec (motive := fun _ => List β) [] (fun x _ ih => List.cons (f x) ih) l

@[expose] noncomputable def eqNLL (a : List (List Nat)) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => bAnd(eqNL x y, ih ys)) b) a

@[expose] noncomputable def sndL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun _ t _ => List.rec (motive := fun _ => Nat) (nat_lit 0) (fun y _ _ => y) t) l

@[expose] noncomputable def rowsK (n b : Nat) (l : List Nat) : Bool :=
  bAnd(Nat.beq (lenL l) n, allL (fun x => Nat.blt x b) l)

@[expose] noncomputable def localShapeK (L : LocalCert) : Bool :=
  bAnd(Nat.beq L.schemaVersion (nat_lit 1),
  bAnd(eqNL L.alignmentOddOrders [nat_lit 3, nat_lit 3],
  bAnd(Nat.beq L.expectedFrattiniRank (nat_lit 5),
  bAnd(eqNL L.expectedCentralizerIndices [nat_lit 56925, nat_lit 1024650],
  bAnd(Nat.beq (lenL L.cInitialWords) (nat_lit 2), bAnd(allL (lettersK (nat_lit 2)) L.cInitialWords,
  bAnd(Nat.beq (lenL L.dWords) (nat_lit 2), bAnd(allL (lettersK (nat_lit 2)) L.dWords,
  bAnd(Nat.beq (lenL L.dStrongDerivations) (nat_lit 5),
  bAnd(wordsL (nat_lit 2) L.dStrongDerivations (nat_lit 0),
  bAnd(Nat.beq (lenL L.rWords) (nat_lit 10), bAnd(allL (lettersK (nat_lit 7)) L.rWords,
  bAnd(lettersK (nat_lit 2) L.cInitialCenterWord, bAnd(lettersK (nat_lit 2) L.dCenterWord,
  bAnd(lettersK (nat_lit 10) L.zRWord, bAnd(lettersK (nat_lit 2) L.alignmentIntermediateWord,
  bAnd(Nat.beq (lenL L.cStrongDerivations) (nat_lit 7),
  bAnd(wordsL (nat_lit 2) L.cStrongDerivations (nat_lit 0),
  bAnd(Nat.beq (lenL L.qWords) (nat_lit 8), bAnd(allL (lettersK (nat_lit 9)) L.qWords,
  bAnd(Nat.beq (lenL L.sQuotientWords) (nat_lit 7),
  bAnd(allL (lettersK (nat_lit 9)) L.sQuotientWords,
  bAnd(Nat.beq (lenL L.frattiniProfiles) (nat_lit 32),
  bAnd(allL (fun p => Nat.beq (lenL p) (nat_lit 12)) L.frattiniProfiles,
  bAnd(chainK L.chains.C (nat_lit 2300) (nat_lit 2) (nat_lit 14)
    [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5],
  bAnd(chainK L.chains.D (nat_lit 2300) (nat_lit 2) (nat_lit 12)
    [nat_lit 1, nat_lit 2, nat_lit 0, nat_lit 3],
  bAnd(chainK L.chains.qAction (nat_lit 512) (nat_lit 2) (nat_lit 17)
    [nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 5, nat_lit 4, nat_lit 7, nat_lit 8, nat_lit 6],
  bAnd(chainK L.chains.rAction (nat_lit 2048) (nat_lit 2) (nat_lit 11)
    [nat_lit 3, nat_lit 1, nat_lit 2, nat_lit 5, nat_lit 8, nat_lit 7, nat_lit 4],
  bAnd(chainK L.chains.S (nat_lit 2300) (nat_lit 15) (nat_lit 23) [nat_lit 0, nat_lit 1, nat_lit 3],
  chainK L.chains.join (nat_lit 2300) (nat_lit 4) (nat_lit 17)
    [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5])))))))))))))))))))))))))))))

@[expose] noncomputable def witShapeK (W : WitCert) : Bool :=
  bAnd(Nat.beq W.wLocal.sixAnchor (nat_lit 29),
  bAnd(eqNL W.wLocal.sixBasisIndices
    [nat_lit 516, nat_lit 1588, nat_lit 1809, nat_lit 1630, nat_lit 312, nat_lit 1801],
  bAnd(eqNL W.wLocal.sixGramRows
    [nat_lit 54, nat_lit 21, nat_lit 59, nat_lit 52, nat_lit 47, nat_lit 29],
  bAnd(Nat.beq (lenL W.wLocal.sixRows) (nat_lit 2),
  bAnd(allL (rowsK (nat_lit 6) (nat_lit 64)) W.wLocal.sixRows,
  bAnd(chainK W.wLocal.sixActionChain (nat_lit 63) (nat_lit 2) (nat_lit 12)
    [nat_lit 0, nat_lit 1, nat_lit 3, nat_lit 7, nat_lit 15, nat_lit 31],
  bAnd(eqNL W.wLocal.qQuotientBasisIndices
    [nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5, nat_lit 6, nat_lit 7, nat_lit 8],
  bAnd(Nat.beq (lenL W.wLocal.qQuotientActionRows) (nat_lit 2),
  bAnd(allL (rowsK (nat_lit 8) (nat_lit 256)) W.wLocal.qQuotientActionRows,
  bAnd(eqNL W.wLocal.dStrongFixedBySIndices [nat_lit 6, nat_lit 7, nat_lit 8],
  bAnd(eqNLL W.wLocal.dCandidateSurvivors [[nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 9]],
  bAnd(Nat.beq (lenL W.wLocal.dAdditionalFixedWords) (nat_lit 1),
  bAnd(allL (lettersK (nat_lit 2)) W.wLocal.dAdditionalFixedWords,
  bAnd(eqNLL W.wLocal.dInnerSurvivors [[nat_lit 0, nat_lit 0], [nat_lit 0, nat_lit 9]],
  bAnd(Nat.beq W.fusion.sylowOrder (nat_lit 262144),
  bAnd(Nat.beq (lenL W.fusion.representatives) (nat_lit 3),
  bAnd(eqNL (mapL WitRep.sylowIndex W.fusion.representatives)
    [nat_lit 44, nat_lit 527, nat_lit 23],
  bAnd(eqNL (mapL WitRep.rankMinusIdentity W.fusion.representatives)
    [nat_lit 6, nat_lit 8, nat_lit 10],
  bAnd(allL (fun r => rowsK (nat_lit 22) (nat_lit 4194304) r.matrixRows) W.fusion.representatives,
  bAnd(eqNLL W.fusion.rankCounts
    [[nat_lit 6, nat_lit 221], [nat_lit 8, nat_lit 1034], [nat_lit 10, nat_lit 4888]],
  bAnd(Nat.beq (lenL W.fusion.fusionBatches) (nat_lit 72),
  bAnd(allL (fun b => bAnd(Nat.blt b.representative (nat_lit 3),
      bAnd(lettersK (nat_lit 2) b.conjugatingWord,
      allL (fun p => bAnd(Nat.beq (lenL p) (nat_lit 2),
        Nat.beq (Nat.mod (sndL p) (nat_lit 2)) (nat_lit 1))) b.pairs)))
    W.fusion.fusionBatches,
  bAnd(Nat.beq (lenL W.third.baseIndices) (nat_lit 13),
  bAnd(distinctL (nat_lit 2300) W.third.baseIndices (nat_lit 0),
  bAnd(Nat.beq (lenL W.third.strongDerivations) (nat_lit 28),
  bAnd(wordsL (nat_lit 2) W.third.strongDerivations (nat_lit 0),
  bAnd(Nat.beq (lenL W.third.fixedPoints) (nat_lit 52),
  bAnd(Nat.beq (lenL W.third.fixedBasis) (nat_lit 12),
  bAnd(Nat.beq (lenL W.third.odd.sylowThreeGenerators) (nat_lit 2),
  bAnd(allL (rowsK (nat_lit 22) (nat_lit 4194304)) W.third.odd.sylowThreeGenerators,
  bAnd(rowsK (nat_lit 22) (nat_lit 4194304) W.third.odd.sylowFiveGenerator,
  bAnd(Nat.beq (lenL W.third.odd.obstructions) (nat_lit 12),
  bAnd(eqNL (mapL WitObstruction.prime W.third.odd.obstructions)
    [nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 3, nat_lit 3,
      nat_lit 5, nat_lit 5, nat_lit 5, nat_lit 5],
  allL (fun o => bAnd(rowsK (nat_lit 22) (nat_lit 4194304) o.element,
      rowsK (nat_lit 22) (nat_lit 4194304) o.conjugator))
    W.third.odd.obstructions)))))))))))))))))))))))))))))))))

end CFSG.KS.Co2SShape

end

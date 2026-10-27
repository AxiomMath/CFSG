module

public import CFSG.Quasithin.Recognition.RuRank3T1Data
public import CFSG.Quasithin.H13.QTESylowThreeNative
public import CFSG.Quasithin.Recognition.RuRank3RuAutDataInputs

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H13.QTESylow CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def t1Ta : Array Nat := titsDArrs[0]!

@[expose] def t1Tb : Array Nat := titsDArrs[1]!

@[expose] def t1Tai : Array Nat := invArr 1755 t1Ta

@[expose] def t1Tbi : Array Nat := invArr 1755 t1Tb

@[expose] def t1Dec : Array Nat × Array Nat × Array Nat × Array Nat :=
  decodeAct 14976 t1Bits t1Targets

@[expose] def t1Aa : Array Nat := t1Dec.1

@[expose] def t1Ab : Array Nat := t1Dec.2.1

@[expose] def decActPar (d : Array Nat × Array Nat × Array Nat × Array Nat) : Array Nat := d.2.2.1

@[expose] def decActGen (d : Array Nat × Array Nat × Array Nat × Array Nat) : Array Nat := d.2.2.2

@[expose] def t1Par : Array Nat := decActPar t1Dec

@[expose] def t1Gen : Array Nat := decActGen t1Dec

@[expose] def t1NT : Array (Array Nat) := slpTabsA t1Ta t1Tb t1Prog

@[expose] def t1RG : List (Array Nat) := t1NQp.map fun p => t1NT[p.1]!

@[expose] def t1RGi : List (Array Nat) := t1NQp.map fun p => t1NT[p.2]!

@[expose] def t1Enum : Array (List Nat) × Array Nat × Array Nat :=
  bfsEnumB 1755 (List.range 1755) t1RG t1RGi 100000

@[expose] def t1Keys : Std.HashMap Nat Nat := keyMap 1755 t1Enum.1

@[expose] def t1T : Array (Array Nat) := treeTabs 1755 14976 t1Ta t1Tb t1Par t1Gen

@[expose] def t1U : Array (Array Nat) := treeInvTabs 1755 14976 t1Tai t1Tbi t1Par t1Gen

@[expose] def t1ONodes : Array (Array Nat) := slpTabsA t1Aa t1Ab t1Prog

@[expose] def t1ROm : List (Array Nat) := t1NQp.map fun p => t1ONodes[p.1]!

@[expose] def t1RepR : Array Nat := orbitReps t1ROm 14976

@[expose] def t1Reps : List Nat := repList 14976 t1RepR

@[expose] def t1Orbs : List (Nat × Array Bool) := repOrbs t1ROm 14976 t1Reps

@[expose] def t1PG : List (Array Nat) := t1PQp.map fun p => t1NT[p.1]!

@[expose] def t1PGi : List (Array Nat) := t1PQp.map fun p => t1NT[p.2]!

@[expose] def t1PEnum : Array (List Nat) × Array Nat × Array Nat :=
  bfsEnumB 1755 (List.range 1755) t1PG t1PGi 1000

@[expose] def t1PKeys : Std.HashMap Nat Nat := keyMap 1755 t1PEnum.1

@[expose] def t1Conj (x : Nat) (g : Array Nat) : Array Nat :=
  compA 1755 (t1T.getD x #[]) (compA 1755 g (t1U.getD x #[]))

@[expose] def t1Gens (x : Nat) : Array (Array Nat) :=
  #[t1NT[194]!, t1NT[260]!, t1Conj x t1NT[194]!, t1Conj x t1NT[260]!]

@[expose] def t1GensInv (x : Nat) : Array (Array Nat) :=
  #[t1NT[217]!, t1NT[303]!, t1Conj x t1NT[217]!, t1Conj x t1NT[303]!]

@[expose] def t1K0Inv : Array (Array Nat) := titsK0Gens.map (invCand 1755)

@[expose] def t1Letter (c : Nat) : Int :=
  if c < 4 then ((c + 1 : Nat) : Int) else -((c - 3 : Nat) : Int)

@[expose] def t1DecWord (len : Nat) (s : String) : List Int :=
  let b := s.toUTF8
  (List.range len).map fun i => t1Letter ((b64Val (b.get! (i / 2)) >>> (3 * (i % 2))) % 8)

@[expose] def t1NormCheck : Bool :=
  t1NQp.all fun s => t1PQp.all fun g =>
    memR 1755 (ptsOf (List.range 1755) t1PG) t1PEnum.1 t1PKeys
      (compA 1755 t1NT[s.1]! (compA 1755 t1NT[g.1]! t1NT[s.2]!))

@[expose] def t1CliqueCheck : Bool :=
  t1Clique.all (fun e =>
    t1RepR.getD e.1 0 == t1Special && t1C.contains e.2.1 &&
      t1GenReps.contains (t1RepR.getD e.2.2 0) && decide (e.2.2 < 14976) &&
      arrImg (omegaOf 14976 t1Aa t1Ab t1Par t1Gen e.2.1 e.2.1) e.2.2 == e.1) &&
  (List.range 14976).all fun i =>
    t1RepR.getD i 0 != t1Special || t1C.contains i || t1Clique.any fun e => e.1 == i

@[expose] def t1CCheck : Bool :=
  t1C.all (fun k => decide (k < 14976) && t1CWords.any fun e => e.1 == k) &&
  t1CWords.all fun e =>
    lettersOK 4 e.2.1 && lettersOK 4 e.2.2 &&
      eqA 1755 (wordA 1755 (t1Gens t1Special) (t1GensInv t1Special) e.2.1)
        (t1Conj e.1 t1NT[194]!) &&
      eqA 1755 (wordA 1755 (t1Gens t1Special) (t1GensInv t1Special) e.2.2)
        (t1Conj e.1 t1NT[260]!)

@[expose] def t1IdCheck : Bool :=
  decide (qpOK 1755 t1NT [t1TNodes]) &&
  (List.range 3).all (fun i => isInvA 1755 titsK0Gens[i]! t1K0Inv[i]!) &&
  t1IdK.length == 4 && t1IdL.length == 3 &&
  (List.range 4).all (fun i =>
    lettersOK 3 t1IdK[i]! &&
      eqA 1755 (wordA 1755 titsK0Gens t1K0Inv t1IdK[i]!)
        (compA 1755 t1NT[t1TNodes.1]! (compA 1755 (t1Gens t1Special)[i]! t1NT[t1TNodes.2]!))) &&
  (List.range 3).all fun i =>
    lettersOK 4 t1IdL[i]! &&
      eqA 1755 (wordA 1755 (t1Gens t1Special) (t1GensInv t1Special) t1IdL[i]!)
        (compA 1755 t1NT[t1TNodes.2]! (compA 1755 titsK0Gens[i]! t1NT[t1TNodes.1]!))

@[expose] def t1Check : Bool :=
  decide (treeValid 14976 t1Par t1Gen) && decide (invValid 1755 t1Ta t1Tb t1Tai t1Tbi) &&
    slpValidAux t1Prog 2 && decide (qpOK 1755 t1NT t1NQp) &&
    decide (BaseEnumOK 1755 (List.range 1755) t1RG t1RGi t1Enum.1 t1Enum.2.1 t1Enum.2.2) &&
    t1Enum.1.size == 1200 && decide (aszOK 14976 t1Aa t1Ab) &&
    edgeOK 1755 14976 (ptsOf (List.range 1755) t1RG) t1Enum.1 t1Keys t1Ta t1Tb t1Aa t1Ab t1T
      t1U &&
    decide (repsOK t1ROm 14976 t1RepR t1Reps t1Orbs) &&
    decide (qpOK 1755 t1NT t1PQp) &&
    decide (BaseEnumOK 1755 (List.range 1755) t1PG t1PGi t1PEnum.1 t1PEnum.2.1 t1PEnum.2.2) &&
    t1PEnum.1.size == 25 && t1PQp == [(194, 217), (260, 303)] && t1NormCheck &&
    t1Reps.all (fun x => x == 0 || x == t1Special || t1GenReps.contains x) &&
    decide (t1Special < 14976) && t1CliqueCheck && t1CCheck && t1IdCheck &&
    t1Ta.size == 1755 && t1Tb.size == 1755

@[expose] def t1GenCheck : Bool :=
  t1GenReps.all (fun x => decide (x < 14976) && t1GenWords.any fun e => e.1 == x) &&
  t1GenWords.all fun e =>
    let w0 := t1DecWord e.2.1 e.2.2.1
    let w1 := t1DecWord e.2.2.2.1 e.2.2.2.2
    lettersOK 4 w0 && lettersOK 4 w1 &&
      eqA 1755 (wordA 1755 (t1Gens e.1) (t1GensInv e.1) w0) t1Ta &&
      eqA 1755 (wordA 1755 (t1Gens e.1) (t1GensInv e.1) w1) t1Tb

end CFSG.Quasithin.RuRank3

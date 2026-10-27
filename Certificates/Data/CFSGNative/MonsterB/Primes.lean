module

public import Certificates.Data.CFSGNative.MonsterB.Max2Pinned

public section

namespace CFSG.Monster.B.Primes.Native

open CFSG.Monster.B.Bin

set_option compiler.extract_closed false

inductive Ins where
  | mu (i j k : Nat)
  | iv (i k : Nat)
  | pwr (e i k : Nat)
deriving Inhabited

@[expose] def Ins.lt (N : Nat) : Ins → Bool
  | .mu i j k => decide (i < N) && decide (j < N) && decide (k < N)
  | .iv i k => decide (i < N) && decide (k < N)
  | .pwr _ i k => decide (i < N) && decide (k < N)

@[expose] def regStep (n : Nat) (st : Array Mat × Bool) : Ins → Array Mat × Bool
  | .mu i j k => (st.1.set! k (mulP n (st.1.getD i #[]) (st.1.getD j #[])), st.2)
  | .iv i k =>
    let X := st.1.getD i #[]
    let Y := invM n X
    (st.1.set! k Y, st.2 && mulP n X Y == idMat n)
  | .pwr e i k => (st.1.set! k (powM n (st.1.getD i #[]) e), st.2)

@[expose] def regsInit (n N : Nat) (A B : Mat) : Array Mat :=
  Array.ofFn (n := N) fun i => if i.val = 1 then A else if i.val = 2 then B else idMat n

@[expose] def regRun (n N : Nat) (prog : List Ins) (A B : Mat) : Array Mat × Bool :=
  prog.foldl (regStep n) (regsInit n N A B, true)

@[expose] def fiveProg (_ : Unit := ()) : List Ins :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 3 5, .mu 5 5 3, .mu 3 4 12, .mu 12 12 3, .mu 12 3 4, .mu 4 4 5,
    .mu 5 5 3, .mu 3 3 10, .mu 1 10 3, .mu 3 3 11, .mu 11 12 3, .mu 3 12 4, .mu 3 3 5, .mu 4 3 6,
    .mu 5 6 7, .mu 7 7 8, .mu 7 8 9, .mu 8 9 13, .mu 3 4 5, .mu 5 5 6, .mu 12 6 7, .mu 7 7 8,
    .mu 8 8 9, .mu 4 6 7, .mu 7 5 3, .iv 3 4, .mu 4 9 5, .mu 5 3 14, .mu 13 14 3, .mu 3 14 4,
    .mu 4 14 5, .mu 5 14 6, .pwr 3 4 15, .mu 5 5 4, .mu 3 3 5, .mu 5 4 7, .pwr 5 7 4, .pwr 20 6 5,
    .pwr 6 3 6, .mu 5 6 3, .iv 3 5, .mu 5 4 6, .mu 6 3 16, .mu 15 16 3, .mu 3 16 4, .mu 3 4 5,
    .mu 3 5 6, .pwr 6 6 7, .iv 15 8, .mu 7 8 9, .mu 7 15 6, .mu 9 6 5, .mu 5 5 6, .mu 15 6 17,
    .iv 16 8, .mu 7 8 9, .pwr 3 7 5, .mu 5 16 6, .mu 9 6 5, .mu 5 5 6, .mu 16 6 18, .mu 17 18 3,
    .mu 3 18 4, .mu 3 4 5, .mu 3 5 6, .pwr 15 6 7, .mu 7 10 19, .mu 1 19 3, .pwr 17 3 20,
    .pwr 6 6 21, .mu 20 21 3, .pwr 4 3 4, .iv 4 5, .mu 21 5 6, .mu 21 4 7, .mu 6 7 8, .mu 8 8 7,
    .mu 4 7 5, .iv 5 4, .mu 21 4 6, .mu 21 5 7, .mu 6 7 8, .mu 8 8 7, .mu 5 7 1, .mu 17 18 2]

@[expose] def threeProg (_ : Unit := ()) : List Ins :=
  [.mu 1 2 3, .mu 3 2 4, .mu 3 3 5, .mu 5 5 3, .mu 3 4 12, .mu 12 12 3, .mu 12 3 4, .mu 4 4 5,
    .mu 5 5 3, .mu 3 3 4, .mu 1 4 3, .mu 3 3 11, .mu 11 12 3, .mu 3 12 4, .mu 3 3 5, .mu 4 3 6,
    .mu 5 6 7, .mu 7 7 8, .mu 7 8 9, .mu 8 9 13, .mu 3 4 5, .mu 5 5 6, .mu 12 6 7, .mu 7 7 8,
    .mu 8 8 9, .mu 4 6 7, .mu 7 5 3, .iv 3 4, .mu 4 9 5, .mu 5 3 14, .mu 13 14 3, .mu 3 14 4,
    .mu 3 4 5, .mu 3 5 6, .mu 6 3 7, .mu 7 4 8, .mu 3 8 9, .mu 5 8 4, .pwr 5 4 15, .pwr 3 5 4,
    .pwr 17 6 5, .pwr 24 9 6, .mu 5 6 7, .iv 7 8, .mu 8 4 6, .mu 6 7 16, .mu 15 16 3, .pwr 10 3 4,
    .iv 15 5, .mu 15 4 6, .iv 4 7, .mu 7 15 8, .mu 6 5 9, .mu 9 8 17, .iv 16 5, .mu 16 4 6,
    .mu 7 16 8, .mu 6 5 9, .mu 9 8 2, .mu 17 2 3, .pwr 15 3 4, .pwr 24 12 5, .mu 4 5 6, .mu 1 6 7,
    .pwr 26 7 1, .pwr 5 3 5, .mu 5 5 3, .mu 1 3 4, .mu 4 4 5, .iv 5 6, .mu 5 3 7, .mu 6 3 8,
    .mu 7 8 9, .mu 9 5 4, .iv 4 6, .mu 4 3 7, .mu 6 3 8, .mu 7 8 9, .mu 9 4 5, .mu 17 5 1]

@[expose] def wordFrom (n : Nat) (A B : Mat) : Mat → List Char → Mat
  | X, [] => X
  | X, c :: w =>
    wordFrom n A B (if c = 'a' then mulP n X A else if c = 'b' then mulP n X B else X) w

@[expose] def word7 : String := "ababbabbab"

@[expose] def word17 : String := "ababbabbababababababb"

@[expose] def word19 : String := "ababbabbababababababbabababb"

@[expose] def word31 : String := "ababbabbababababababbabababbabababb"

@[expose] def word47 : String :=
  "ababbabbababababababbabababbabababbababbabbababababbabbababbabbab"

@[expose] def word13 : String :=
  "ababbabbababababababbabababbabababbababbabbababababbabbababbabbababbabababb"

@[expose] def ordOK (n p : Nat) (X : Mat) : Bool := powM n X p == idMat n && neM n X (idMat n)

@[expose] def ordExactOK (n e : Nat) (rs : List Nat) (X : Mat) : Bool :=
  powM n X e == idMat n && rs.all fun r => neM n (powM n X (e / r)) (idMat n)

@[expose] def powTable (n p : Nat) (X : Mat) : List Mat := (List.range p).map (powM n X)

@[expose] def prodPows (n : Nat) : List (List Mat) → List Nat → Mat
  | T :: Ts, e :: es => if e = 0 then prodPows n Ts es else mulP n (T.getD e #[]) (prodPows n Ts es)
  | _, _ => idMat n

@[expose] def mulTab (n : Nat) (P : Mat) (Z : List Mat) (c : Nat) : Mat :=
  if c = 0 then P else mulP n P (Z.getD c #[])

@[expose] def commDataOK (n p : Nat) (qs : List Mat) (z : Mat) (Z : List Mat)
    (Mr : List (List Nat)) : Bool :=
  let qi := qs.map (powM n · (p - 1))
  qs.all (ordOK n p) && ordOK n p z && qs.all (fun q => mulP n q z == mulP n z q) &&
  (List.range qs.length).all fun i => (List.range qs.length).all fun j =>
    !(decide (i < j)) ||
      mulP n (mulP n (mulP n (qi.getD i #[]) (qi.getD j #[])) (qs.getD i #[])) (qs.getD j #[]) ==
        Z.getD ((Mr.getD i []).getD j 0) #[]

@[expose] def actOK (n : Nat) (qs : List Mat) (T : List (List Mat)) (Z : List Mat) (b bi : Mat)
    (R : List (List Nat)) (c : List Nat) : Bool :=
  (List.range qs.length).all fun i =>
    mulP n (mulP n bi (qs.getD i #[])) b ==
      mulTab n (prodPows n T (R.getD i [])) Z (c.getD i 0)

@[expose] def sha7 (_ : Unit := ()) : Nat := 0x80a35ce7456365c0a505cc692d8a8fe0b3a3a54d46249da0d68ea0c87a2922bd

@[expose] def sha13 (_ : Unit := ()) : Nat := 0x9c1870299022a06b87110d4545446435e8ab03540c709ac23a95cf41b6302cc2

@[expose] def sha17 (_ : Unit := ()) : Nat := 0xebe65f3e4a0959c62f5b7eff558d05b0e4e2a29c89fa7d2125bfb46787405dd4

@[expose] def sha19 (_ : Unit := ()) : Nat := 0x4c9c5cfcb0313c0b4032d706770b553ef448c88de8166ae92571a51bfbfd19dc

@[expose] def sha31 (_ : Unit := ()) : Nat := 0x0fd5280ace30af3848f55e4f6e049911e2d810c36336e8b232b9e812189e1d16

@[expose] def sha47 (_ : Unit := ()) : Nat := 0x45597aead4a29578bf71035e134c551920871a63aae2d5d291d96f3721405dc3

@[expose] def primeOK (n p : Nat) (G : Mat) (sha : Nat) : Bool :=
  ordOK n p G && Binary.Native.sha256Nat (payload n #[G]) == sha

@[expose] def sixChecks (n : Nat) (A B : Mat) : Bool :=
  let W7 := wordFrom n A B (idMat n) word7.toList
  let W17 := wordFrom n A B W7 (word17.toList.drop 10)
  let W19 := wordFrom n A B W17 (word19.toList.drop 21)
  let W31 := wordFrom n A B W19 (word31.toList.drop 28)
  let W47 := wordFrom n A B W31 (word47.toList.drop 35)
  let W13 := wordFrom n A B W47 (word13.toList.drop 65)
  primeOK n 7 (powM n W7 1) sha7 && primeOK n 13 (powM n W13 2) sha13 &&
    primeOK n 17 (powM n W17 2) sha17 && primeOK n 19 (powM n W19 1) sha19 &&
    primeOK n 31 (powM n W31 1) sha31 && primeOK n 47 (powM n W47 1) sha47

@[expose] def fiveSha (_ : Unit := ()) : Nat := 0xa82afd335ad2953a74490c5b8dd0ea46cc3ccf617daf097bf2bb75b689e53b2b

@[expose] def fiveChecks (n : Nat) (A B : Mat) (Mr Ar : List (List Nat)) (ac : List Nat) : Bool :=
  let R := regRun n 22 fiveProg A B
  let x := R.1.getD 1 #[]
  let h := R.1.getD 2 #[]
  let xi := powM n x 4
  let hi := powM n h 7
  let w := mulP n x (powM n h 3)
  let q1 := powM n w 8
  let q2 := mulP n (mulP n hi q1) h
  let q3 := mulP n (mulP n xi q1) x
  let q4 := mulP n (mulP n xi q2) x
  let qs := [q1, q2, q3, q4]
  let z := mulP n (mulP n (mulP n (powM n q1 4) (powM n q2 4)) q1) q2
  let Z := powTable n 5 z
  let T := qs.map (powTable n 5)
  R.2 && ordExactOK n 5 [5] x && ordExactOK n 8 [2] h && ordExactOK n 40 [2, 5] w &&
    commDataOK n 5 qs z Z Mr && mulP n x z == mulP n z x &&
    actOK n qs T Z x xi Ar ac &&
    Binary.Native.sha256Nat (payload n #[q1, q2, q3, q4, z, x]) == fiveSha

@[expose] def threeSha (_ : Unit := ()) : Nat := 0xfd478aa064a3334e430eb0570049bc72e123b9ba9c0942a63de1e8ffdce8d9aa

@[expose] def conjM (n : Nat) (Y b bi : Mat) : Mat := mulP n (mulP n bi Y) b

@[expose] def threeChecks (n : Nat) (A B : Mat) (Mr Xr Yr : List (List Nat)) (c d : List Nat) :
    Bool :=
  let R := regRun n 18 threeProg A B
  let x := R.1.getD 1 #[]
  let h := R.1.getD 2 #[]
  let xi := powM n x 39
  let hi := powM n h 7
  let x20 := powM n x 20
  let q1 := mulP n x20 (conjM n x20 h hi)
  let q2 := conjM n q1 x xi
  let q3 := conjM n q1 h hi
  let q4 := conjM n q2 x xi
  let q5 := conjM n q2 h hi
  let q6 := conjM n q3 x xi
  let q7 := conjM n q3 h hi
  let q8 := conjM n q4 x xi
  let qs := [q1, q2, q3, q4, q5, q6, q7, q8]
  let z := mulP n (mulP n (mulP n (powM n q1 2) (powM n q2 2)) q1) q2
  let Z := powTable n 3 z
  let T := qs.map (powTable n 3)
  let h4 := powM n h 4
  let r17 := powM n (R.1.getD 17 #[]) 4
  let r15 := powM n (R.1.getD 15 #[]) 2
  let seeds := #[mulP n h4 (conjM n h4 x xi), q1, mulP n r17 (conjM n r17 x xi),
    mulP n r17 (conjM n r17 h hi), mulP n r15 (conjM n r15 x xi), mulP n r15 (conjM n r15 h hi)]
  R.2 && ordExactOK n 40 [2, 5] x && ordExactOK n 8 [2] h &&
    commDataOK n 3 qs z Z Mr &&
    conjM n z x xi == mulP n z z && conjM n z h hi == mulP n z z &&
    actOK n qs T Z x xi Xr c && actOK n qs T Z h hi Yr d &&
    Binary.Native.sha256Nat
        (payload n (#[x, h] ++ seeds ++ #[q1, q2, z, q3, q4, q5, q6, q7, q8, z])) == threeSha

@[expose] def sixOK (_ : Unit := ()) : Bool :=
  sixChecks 4370 (seedMat 4370 CFSG.SectionRank.Native.bData.seedA)
    (seedMat 4370 CFSG.SectionRank.Native.bData.seedB)

end CFSG.Monster.B.Primes.Native

module

public import Certificates.Data.ONanCMNormal

public section

namespace CFSG.OddStandard.ONanRec.CM

@[expose] def chainAll (p : Tab → Bool) : Tab → List ChainLevel → Bool
  | acc, [] => p acc
  | acc, L :: rest =>
    L.words.all fun qw => chainAll p (compTab 480 acc (wordTab 480 cmLetters qw.2)) rest

@[expose] def tabOf (w : List Nat) : Tab := wordTab 480 cmLetters w

@[expose] def wpow (w : List Nat) (n : Nat) : List Nat := (List.replicate n w).flatten

@[expose] def commTab (s t : Tab) : Bool := compTab 480 s t == compTab 480 t s

@[expose] def ord4Tab (t : Tab) : Bool :=
  compTab 480 (compTab 480 t t) (compTab 480 t t) == idTab 480 && !(compTab 480 t t == idTab 480)

@[expose] def yW : List Nat := [11, 4, 10, 4]

@[expose] def zW : List Nat := [11, 6, 10, 6]

@[expose] def dW : List Nat := [6]

@[expose] def fW : List Nat := [8]

@[expose] def gW : List Nat := [10]

@[expose] def r1W : List Nat := [0, 2]

@[expose] def r2W : List Nat := invWord yW ++ r1W ++ yW

@[expose] def rW (i j : Nat) : List Nat := wpow r1W i ++ wpow r2W j

@[expose] def rWords : List (List Nat) :=
  (List.range 3).flatMap fun i => (List.range 3).map fun j => rW i j

@[expose] def sW (k l : Nat) : List Nat := wpow zW k ++ wpow dW l

@[expose] def sWords : List (List Nat) :=
  (List.range 4).flatMap fun k => (List.range 2).map fun l => sW k l

@[expose] def rsWords : List (List Nat) :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    (List.range 4).flatMap fun k => (List.range 2).map fun l => rW i j ++ sW k l

@[expose] def oddWords : List (List Nat) :=
  (List.range 3).flatMap fun i => (List.range 3).flatMap fun j =>
    [1, 3].flatMap fun k => (List.range 2).map fun l => rW i j ++ wpow yW k ++ wpow fW l

@[expose] def centerLeaf (fT t : Tab) : Bool :=
  !((List.range 6).all fun i => commTab cmLetters[2 * i]! t) || t == idTab 480 || t == fT

@[expose] def centRLeaf (r1T r2T : Tab) (rsT : List Tab) (t : Tab) : Bool :=
  !(commTab t r1T && commTab t r2T) || rsT.contains t

@[expose] def centSLeaf (zT dT : Tab) (oddT : List Tab) (t : Tab) : Bool :=
  !(commTab t zT && commTab t dT) || !ord4Tab t || oddT.contains t

@[expose] def b2Leaf (fT r1T r2T zT dT : Tab) (rsT oddT : List Tab) (t : Tab) : Bool :=
  centerLeaf fT t && centRLeaf r1T r2T rsT t && centSLeaf zT dT oddT t

@[expose] def b2ChainCheck : Bool :=
  chainAll (b2Leaf (tabOf fW) (tabOf r1W) (tabOf r2W) (tabOf zW) (tabOf dW)
    (rsWords.map tabOf) (oddWords.map tabOf)) (idTab 480) cmChain

@[expose] def tGens : List (List Nat) := [yW, dW, gW]

@[expose] def tWord (l : List Nat) : List Nat := l.flatMap fun k => tGens[k]!

@[expose] def tIdx : List (List Nat) :=
  [[], [0], [1], [2], [0, 0], [0, 1], [0, 2], [1, 2], [2, 0], [2, 1], [2, 2], [0, 0, 0],
    [0, 0, 1], [0, 0, 2], [0, 1, 2], [0, 2, 1], [0, 2, 2], [1, 2, 0], [1, 2, 1], [1, 2, 2],
    [2, 0, 1], [2, 0, 2], [2, 1, 2], [2, 2, 2], [0, 0, 0, 1], [0, 0, 1, 2], [0, 0, 2, 1],
    [0, 0, 2, 2], [0, 1, 2, 1], [0, 1, 2, 2], [0, 2, 1, 2], [0, 2, 2, 2], [1, 2, 0, 1],
    [1, 2, 0, 2], [1, 2, 1, 2], [1, 2, 2, 2], [2, 0, 1, 2], [2, 0, 2, 2], [2, 1, 2, 1],
    [2, 1, 2, 2], [0, 0, 1, 2, 1], [0, 0, 1, 2, 2], [0, 0, 2, 1, 2], [0, 0, 2, 2, 2],
    [0, 1, 2, 1, 2], [0, 1, 2, 2, 2], [0, 2, 1, 2, 1], [0, 2, 1, 2, 2], [1, 2, 0, 1, 2],
    [1, 2, 0, 2, 2], [1, 2, 1, 2, 1], [1, 2, 1, 2, 2], [2, 0, 1, 2, 1], [2, 0, 1, 2, 2],
    [2, 1, 2, 2, 2], [0, 0, 1, 2, 1, 2], [0, 0, 1, 2, 2, 2], [0, 0, 2, 1, 2, 1],
    [0, 0, 2, 1, 2, 2], [0, 1, 2, 1, 2, 1], [0, 1, 2, 1, 2, 2], [0, 2, 1, 2, 2, 2],
    [1, 2, 0, 1, 2, 2], [0, 0, 1, 2, 1, 2, 2]]

@[expose] def qWords : List (List Nat) :=
  (List.range 4).flatMap fun k => (List.range 2).map fun l => wpow yW k ++ wpow fW l

@[expose] def wPowWords (w : List Nat) : List (List Nat) := (List.range 4).map (wpow w)

@[expose] def swWords (w : List Nat) : List (List Nat) :=
  (List.range 4).flatMap fun k => (List.range 2).flatMap fun l =>
    (List.range 4).map fun m => sW k l ++ wpow w m

@[expose] def b2LettersOK : Bool :=
  (([yW, zW, dW, fW, gW, r1W, r2W] ++ rsWords ++ oddWords ++ qWords ++ swWords yW ++
    swWords (yW ++ fW) ++ tIdx.map tWord).all fun w => w.all (· < 12))

@[expose] def fzOK : Bool :=
  ((List.range 6).all fun i => commTab cmLetters[2 * i]! (tabOf fW)) &&
    (compTab 480 (tabOf zW) (tabOf zW) == tabOf fW) &&
    ((List.range 6).all fun i =>
      tabOf ([2 * i] ++ zW ++ [2 * i + 1]) == tabOf zW ||
        tabOf ([2 * i] ++ zW ++ [2 * i + 1]) == tabOf (invWord zW))

@[expose] def rOK : Bool :=
  (tabOf (wpow r1W 3) == idTab 480) && (tabOf (wpow r2W 3) == idTab 480) &&
    commTab (tabOf r1W) (tabOf r2W) && decide (rWords.map tabOf).Nodup &&
    (tabOf (yW ++ r1W ++ invWord yW) == tabOf (rW 0 2)) &&
    (tabOf (yW ++ r2W ++ invWord yW) == tabOf (rW 1 0))

@[expose] def irredOK : Bool :=
  (List.range 3).all fun i => (List.range 3).all fun j =>
    (i == 0 && j == 0) ||
      (!(tabOf (yW ++ rW i j ++ invWord yW) == idTab 480) &&
        !(tabOf (yW ++ rW i j ++ invWord yW) == tabOf (rW i j)) &&
        !(tabOf (yW ++ rW i j ++ invWord yW) == tabOf (rW i j ++ rW i j)))

@[expose] def sOK : Bool :=
  commTab (tabOf zW) (tabOf r1W) && commTab (tabOf zW) (tabOf r2W) &&
    commTab (tabOf dW) (tabOf r1W) && commTab (tabOf dW) (tabOf r2W) &&
    (tabOf (wpow zW 4) == idTab 480) && !(compTab 480 (tabOf zW) (tabOf zW) == idTab 480) &&
    (compTab 480 (tabOf dW) (tabOf dW) == idTab 480) &&
    (tabOf (dW ++ zW ++ dW) == tabOf (invWord zW)) &&
    !((List.range 4).any fun k => tabOf dW == tabOf (wpow zW k))

@[expose] def tTabs : List Tab := tIdx.map fun l => tabOf (tWord l)

@[expose] def tOK : Bool :=
  decide tTabs.Nodup &&
    (tTabs.all fun t => tGens.all fun s => tTabs.contains (compTab 480 t (tabOf s))) &&
    (tGens.all fun s => [r1W, r2W].all fun r =>
      (rWords.map tabOf).contains (tabOf (s ++ r ++ invWord s)) &&
        (rWords.map tabOf).contains (tabOf (invWord s ++ r ++ s)))

@[expose] def tCentOK : Bool :=
  (tTabs.all fun t =>
    !(commTab t (tabOf zW) && commTab t (tabOf dW)) || (qWords.map tabOf).contains t) &&
  ([yW, yW ++ fW].all fun w => tTabs.all fun t =>
    !((wPowWords w).map tabOf).contains (compTab 480 t t) || ((swWords w).map tabOf).contains t)

@[expose] def yOK : Bool :=
  (tabOf (wpow yW 4) == idTab 480) && !(compTab 480 (tabOf yW) (tabOf yW) == idTab 480)

@[expose] def b2SmallCheck : Bool :=
  b2LettersOK && fzOK && rOK && irredOK && sOK && tOK && tCentOK && yOK

end CFSG.OddStandard.ONanRec.CM

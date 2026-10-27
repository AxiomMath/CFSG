module

public import Certificates.Data.Kernel.HJ12K
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12ThreeThreeCheck

public section

noncomputable section

namespace Certificates.Kernel.HJ12K

open CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

@[expose] def bitQ (m n : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1

@[expose] def acL : List ℕ := [2, 1, 4, 128, 272, 1792, 327, 8, 256, 512, 800, 2952]

@[expose] def bcL : List ℕ := [5, 64, 1, 8, 10, 207, 24, 233, 413, 751, 2656, 3696]

@[expose] def stepO (acc : List ℕ × ℕ) (t : ℕ) : List ℕ × ℕ :=
  match acc with
  | (l, m) => if bitQ m t then (l, m) else (t :: l, Nat.lor m (Nat.shiftLeft 1 t))

@[expose] def roundO (fs : List (ℕ → ℕ)) (fr : List ℕ) (m : ℕ) : List ℕ × ℕ :=
  (fr.flatMap fun s => fs.map fun f => f s).foldl stepO ([], m)

@[expose] def closO (fs : List (ℕ → ℕ)) : ℕ → List ℕ → ℕ → List ℕ → List ℕ
  | 0, fr, _, vis => fr ++ vis
  | fuel + 1, fr, m, vis =>
    let r := roundO fs fr m
    if r.1.isEmpty then fr ++ vis else closO fs fuel r.1 r.2 (fr ++ vis)

@[expose] def orbitQ (p : ℕ) : List ℕ :=
  closO [mvNR acL, mvNR bcL] 4096 [p] (Nat.shiftLeft 1 p) []

@[expose] def maskOf (m : ℕ) (L : List ℕ) : ℕ := L.foldl (fun m x => Nat.lor m (Nat.shiftLeft 1 x)) m

@[expose] def tauQ : ℕ := codeQ hjTauc.toList

@[expose] def isInvolQ (x : ℕ) : Bool := !Nat.beq x oneQ && Nat.beq (mulQ x x) oneQ

@[expose] def commQ (x y : ℕ) : Bool := Nat.beq (mulQ x y) (mulQ y x)

@[expose] def tauQCheck : Bool :=
  invOKQ tauQ (invQ tauQ) &&
    Nat.beq (mulQ (mulQ tauQ acQ) (invQ tauQ)) (wordQ (hj_tauConjWords.headD [])) &&
    Nat.beq (mulQ (mulQ tauQ bcQ) (invQ tauQ)) (wordQ (hj_tauConjWords.getD 1 []))

@[expose] def e16q (C : List ℕ) (s r a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) : Bool :=
  C.any fun q => !(Nat.beq q a0 || (Nat.beq q a1 || (Nat.beq q a2 || (Nat.beq q a3 ||
    (Nat.beq q a4 || (Nat.beq q a5 || (Nat.beq q a6 || (Nat.beq q a7 || false)))))))) &&
      commQ q s && commQ q r

@[expose] def e16r (C : List ℕ) (t s ts : ℕ) : Bool :=
  C.any fun r => !(Nat.beq r oneQ || (Nat.beq r t || (Nat.beq r s || (Nat.beq r ts || false)))) &&
    commQ r s &&
      e16q C s r oneQ t s ts (mulQ oneQ r) (mulQ t r) (mulQ s r) (mulQ ts r)

@[expose] def e16Q (I : List ℕ) (t : ℕ) : Bool :=
  (I.filter fun s => !Nat.beq s t && commQ s t).any fun s =>
    e16r (I.filter fun s => !Nat.beq s t && commQ s t) t s (mulQ t s)

@[expose] def fixOK (M t : ℕ) : Bool :=
  Nat.beq (fixCnt t) 64 ||
    (Nat.beq (fixCnt t) 256 && (fixQ t).any fun s₁ => bitQ M s₁ &&
      (fixQ t).any fun s₂ => bitQ M s₂ && bitQ M (s₁ ^^^ s₂))

@[expose] def t1At (M : ℕ) (g0 g1 a1 a2 X0 X1 A1 A2 : List ℕ) : Bool :=
  gensOKQ g1 && gensOKQ (a1 ++ a2) &&
    closedQ g0 X0 && closedQ g1 X1 && nodupP X0 && Nat.beq X0.length 128 &&
    nodupP X1 && Nat.beq X1.length 256 &&
    closedQ a1 A1 && closedQ a2 A2 && nodupP A1 && Nat.beq A1.length 16 &&
    nodupP A2 && Nat.beq A2.length 16 &&
    A1.all (fun x => X0.contains x && Nat.beq (mulQ x x) oneQ) &&
    A2.all (fun x => X0.contains x && Nat.beq (mulQ x x) oneQ) &&
    A1.all (fun x => A1.all fun y => commQ x y) && A2.all (fun x => A2.all fun y => commQ x y) &&
    A1.any (fun x => !A2.contains x) &&
    ((X1.filter isInvolQ).filter fun t => !A1.contains t && !A2.contains t).all
      (fun t => !e16Q (X1.filter isInvolQ) t) &&
    (X1.filter isInvolQ).all (fixOK M)

@[expose] def g0Q : List ℕ := hj_t0Words.map wordQ

@[expose] def t1Q : Bool :=
  t1At (maskOf 0 (orbitQ 1024)) g0Q (g0Q ++ [tauQ]) (hj_a1Words.map wordQ)
    (hj_a2Words.map wordQ) (enumQ g0Q) (enumQ (g0Q ++ [tauQ])) (enumQ (hj_a1Words.map wordQ))
    (enumQ (hj_a2Words.map wordQ))

@[expose] def rowAux (x : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | y :: I, j => Nat.lor (if commQ x y then Nat.shiftLeft 1 j else 0) (rowAux x I (j + 1))

abbrev Tup : Type := ℕ × ℕ × ℕ × ℕ

@[expose] def tupAux (I : List ℕ) : List ℕ → ℕ → List Tup
  | [], _ => []
  | x :: L, i => (x, i, rowAux x I 0, fixCnt x) :: tupAux I L (i + 1)

@[expose] def mixQ (S64 S256 : NT ℕ) (a b ab c : ℕ) : Bool :=
  [a, b, ab, c, mulQ c a, mulQ c b, mulQ ab c].any (memP S64) &&
    [a, b, ab, c, mulQ c a, mulQ c b, mulQ ab c].any (memP S256)

@[expose] def zLoop (T : List Tup) (S64 S256 : NT ℕ) (p q : Tup) (ab : ℕ) : Bool :=
  T.all fun r => Nat.beq p.1 r.1 || Nat.beq q.1 r.1 || !bitQ p.2.2.1 r.2.1 ||
    !bitQ q.2.2.1 r.2.1 ||
    (Nat.beq r.1 oneQ || (Nat.beq r.1 p.1 || (Nat.beq r.1 q.1 || (Nat.beq r.1 ab || false)))) ||
    !Nat.beq q.2.2.2 r.2.2.2 || mixQ S64 S256 p.1 q.1 ab r.1

@[expose] def triAt (T : List Tup) (S64 S256 : NT ℕ) : Bool :=
  T.all fun p => T.all fun q =>
    (Nat.beq p.1 q.1 || !bitQ p.2.2.1 q.2.1 || !Nat.beq p.2.2.2 q.2.2.2) ||
      zLoop T S64 S256 p q (mulQ p.1 q.1)

@[expose] def setOf (I : List ℕ) (n : ℕ) : NT ℕ := ofListP (I.filter fun x => Nat.beq (fixCnt x) n)

@[expose] def triI (I : List ℕ) : Bool := triAt (tupAux I I 0) (setOf I 64) (setOf I 256)

@[expose] def triQ : Bool := triI ((enumQ (g0Q ++ [tauQ])).filter isInvolQ)

@[expose] def zCore (z : ℕ) : Bool := isInvolQ z && Nat.beq (fixCnt z) 256

@[expose] def zQ : Bool := zCore (wordQ hj_zWord)

@[expose] def fourQ (b1 b2 g v : ℕ) : Bool :=
  isInvolQ b1 && isInvolQ b2 && !Nat.beq b1 b2 && commQ b1 b2 &&
    Nat.beq (mvNR (unpackQ b1) v) v && Nat.beq (mvNR (unpackQ b2) v) v &&
    !Nat.beq (mvNR (unpackQ g) v) v

end Certificates.Kernel.HJ12K

end

end

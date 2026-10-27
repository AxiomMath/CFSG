module

public import CFSG.Quasithin.Background.B3J
public import CFSG.Quasithin.Background.B3CaseA
public import CFSG.Quasithin.Background.B3CaseB

public section

namespace CFSG.Quasithin.B3

@[expose] def rankOK (n : ℕ) (k : Mod) (L : List Tab) (r s : ℕ) : Bool :=
  L.length == 2 ^ r && cntF n k L * 2 ^ s == cntF n k [idT n]

@[expose] def rkPair (n : ℕ) (k : Mod) (L : List Tab) : ℕ × ℕ :=
  (Nat.log 2 L.length, Nat.log 2 (cntF n k [idT n] / cntF n k L))

@[expose] def chkRanksA (n : ℕ) (k : Mod) : Bool :=
  (List.range (n / 2)).all (fun i => rankOK n k (AmL n (i + 1)) (i + 1) (i + 1))

@[expose] def chkRanksB (n : ℕ) (k : Mod) : Bool :=
  (List.range (n / 2)).all (fun i =>
    rankOK n k (AmL n (i + 1)) (i + 1) (if i + 1 == n / 2 then n / 2 - 1 else i + 1)) &&
  rankOK n k (A0L n) (n / 2) (n / 2)

@[expose] def chkE8rank (n : ℕ) (k : Mod) : Bool :=
  (Dl n).all (fun C => !(isE8T n C) || rankOK n k C 3 3)

@[expose] def qRow (n : ℕ) (k : Mod) (snum sden : ℕ) (L : List Tab) : Bool :=
  rankOK n k L (rkPair n k L).1 (rkPair n k L).2 && decide (0 < (rkPair n k L).1) &&
    decide (snum * (rkPair n k L).1 ≤ sden * (rkPair n k L).2)

@[expose] def qWit (n : ℕ) (k : Mod) (snum sden : ℕ) (L : List Tab) : Bool :=
  decide (sden * (rkPair n k L).2 ≤ snum * (rkPair n k L).1)

@[expose] def chkQA (n : ℕ) (k : Mod) : Bool :=
  ((Dl n).filter (isRepA n)).all (qRow n k 1 1) && ((Dl n).filter (isRepA n)).any (qWit n k 1 1)

@[expose] def chkQB (n : ℕ) (k : Mod) : Bool :=
  ((Dl n).filter (isRepB n k)).all (qRow n k (n - 2) n) &&
    ((Dl n).filter (isRepB n k)).any (qWit n k (n - 2) n)

@[expose] def chkStrong (n : ℕ) (k : Mod) : Bool :=
  let DF := mkDF n k (Dl n)
  (Dl n).all (fun C => !(offP DF (C, Fval n k C)) ||
    (decide (cntF n k [idT n] < Fval n k C) == seteqT C (Dc n)))

@[expose] def suppCardT (t : Tab) : ℕ := (List.range t.length).countP (fun i => t.getD i 0 != i)

@[expose] def DT (n : ℕ) : List Tab :=
  (Tl n).filter (fun t => mulT t t == idT n && suppCardT t == 4)

@[expose] def t12 (n : ℕ) : Tab := tab (ti n 0 * ti n 1)

@[expose] def chkDT (n : ℕ) : Bool :=
  suppCardT (t12 n) == 4 && mulT (t12 n) (t12 n) == idT n &&
  (let mp := classMap n (sgensOf n) [t12 n]
   (DT n).all (fun t => match mp.get? [t] with
     | some g => isTab n g && cjT g (t12 n) == t
     | none => false))

@[expose] def chkGenTabs (n : ℕ) (gens : List Tab) : Bool :=
  let S := closeT n gens
  subOK n S && gens.all (fun g => S.contains g) && chainOK gens (idT n) [] S

@[expose] def chkJA (n : ℕ) (k : Mod) : Bool := chkJ n k && seteqT (Jc n k) (Dc n)

@[expose] def chkJ5 (n : ℕ) (k : Mod) : Bool :=
  chkJ n k && chkGenTabs n (Dc n ++ DT n) && seteqT (Jc n k) (closeT n (Dc n ++ DT n)) && chkDT n

@[expose] def chkJ6 (n : ℕ) (k : Mod) : Bool := chkJ n k && seteqT (Jc n k) (Tl n)

@[expose] def chkInT (n : ℕ) : Bool :=
  (List.range (n / 2)).all (fun i => (AmL n (i + 1)).all (fun t => (Tl n).contains t))

@[expose] def chkInT0 (n : ℕ) : Bool :=
  chkGen n (gensA0 n) && (A0L n).all (fun t => (Tl n).contains t)

@[expose] def chkTwoA (n : ℕ) (k : Mod) (e m : ℕ) : Bool :=
  chkA n k e m && chkInT n && chkInT0 n && chkRanksA n k && chkQA n k && chkJA n k

@[expose] def chkTwoB5 (n : ℕ) (k : Mod) (e m : ℕ) : Bool :=
  chkB n k e m && chkInT n && chkInT0 n && chkRanksB n k && chkQB n k && chkStrong n k &&
    chkJ5 n k

@[expose] def chkTwoB6 (n : ℕ) (k : Mod) (e m : ℕ) : Bool :=
  chkB n k e m && chkInT n && chkInT0 n && chkRanksB n k && chkE8rank n k && chkQB n k &&
    chkStrong n k && chkJ6 n k

end CFSG.Quasithin.B3

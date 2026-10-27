module

public import CFSG.Monster.B.Final.Simple
public import CFSG.Monster.B.Rep4371.ExactActions
public import CFSG.Monster.B.Final.Max2Nodes
public import CFSG.Monster.B.Pinned.Primes.FiveSubgroup
public import CFSG.Monster.B.Pinned.Primes.SixPrimes
public import CFSG.Monster.B.Pinned.Primes.ThreeTwelve
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Bridge.BSeven

public section

namespace CFSG.Sporadic.Bridge.B

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Monster.B.Bin
  CFSG.Monster.B.Primes.Native
open scoped Matrix

@[expose] def genRows (i : ℕ) (pos : Bool) : List (List ℕ) :=
  if i = 0 then (if pos then threeXRows else threeXiRows)
  else (if pos then threeYRows else threeYiRows)

@[expose] def wordRows (w : List (ℕ × Bool)) : List (List ℕ) :=
  w.foldl (fun acc l => lmul acc (genRows l.1 l.2)) (lpow threeXRows 0)

@[expose] def w1 : List (ℕ × Bool) :=
  [(0, true), (1, false), (1, false), (1, false), (0, false), (1, true), (1, true), (1, true),
    (0, false), (1, true)]

@[expose] def w2 : List (ℕ × Bool) :=
  [(0, true), (1, true), (0, false), (0, false), (1, true), (0, true), (1, true), (0, false),
    (1, false), (1, false), (0, false), (1, true)]

end CFSG.Sporadic.Bridge.B

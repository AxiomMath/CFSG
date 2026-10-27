module

public import Certificates.Data.Kernel.RouteP.TextSlp

public section

namespace CFSG.KC.RouteP

open CFSG.KC.Str

@[expose] def split2K (a b : Char) : List Char → List Char → Bool → List (List Char)
  | [], acc, false => [acc.reverse]
  | [], acc, true => [(a :: acc).reverse]
  | c :: t, acc, false => if c == a then split2K a b t acc true else split2K a b t (c :: acc) false
  | c :: t, acc, true =>
    if c == b then acc.reverse :: split2K a b t [] false
    else if c == a then split2K a b t (a :: acc) true else split2K a b t (c :: a :: acc) false

@[expose] def natsL (l : List Char) : List Nat := (splitK ' ' l).filterMap tokNat

@[expose] def natsOKL (l : List Char) : Bool := (splitK ' ' l).all fun t => t.isEmpty || digitsL t

@[expose] def m24WordL (b : List Char) : List (Nat × Bool) :=
  b.filterMap fun ch => if ch = '0' then some (0, true) else
    if ch = '1' then some (1, true) else none

@[expose] def treeStepL (a : List (List (Nat × Bool))) (l : List Char) :
    List (List (Nat × Bool)) :=
  match splitK ' ' l with
  | [u, v, bits] => a.set (24 * decVal u + decVal v) (m24WordL bits)
  | _ => a

@[expose] def treeTabL (cs : List Char) : List (List (Nat × Bool)) :=
  (splitK '\n' cs).foldl treeStepL (List.replicate 576 [])

@[expose] def treeOKL (cs : List Char) : Bool :=
  (splitK '\n' cs).all fun l =>
    match splitK ' ' l with
    | [u, v, _] => digitsL u && digitsL v
    | _ => true

@[expose] def comboEntL (l : List Char) : Option (Nat × Nat × Nat) :=
  match natsL l with
  | [p, i, m] => some (p, i, m)
  | _ => none

@[expose] def comboDataL (cs : List Char) : List (List (Nat × Nat × Nat)) :=
  ((split2K 'C' '\n' cs [] false).drop 1).map fun blk => (splitK '\n' blk).filterMap comboEntL

@[expose] def comboOKL (cs : List Char) : Bool :=
  ((split2K 'C' '\n' cs [] false).drop 1).all fun blk => (splitK '\n' blk).all natsOKL

@[expose] def bezLinesL (cs : List Char) : List (List Char) :=
  (splitK '\n' cs).filter (· != [])

@[expose] def sEntL (l : List Char) : Option (Nat × Nat) :=
  match natsL l with
  | [a, b] => some (a, b)
  | _ => none

@[expose] def sDataL (cs : List Char) : List (Nat × Nat) :=
  (((bezLinesL cs).drop 1).takeWhile (· != ['T'])).filterMap sEntL

@[expose] def tDataL (cs : List Char) : List (List Nat) :=
  (((bezLinesL cs).dropWhile (· != ['T'])).drop 1).map natsL

@[expose] def bezOKL (cs : List Char) : Bool :=
  (((bezLinesL cs).drop 1).takeWhile (· != ['T'])).all natsOKL &&
    (((bezLinesL cs).dropWhile (· != ['T'])).drop 1).all natsOKL

end CFSG.KC.RouteP

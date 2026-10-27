module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.SLPProd
public import Certificates.Data.Kernel.KDenseP.Words
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.Monster.B.TwoA.Unitary.Semilinear
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace CFSG.KC.NortonSLPK

open CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton

@[expose] def splitK (c : Char) : List Char → List Char → List (List Char)
  | [], acc => [acc.reverse]
  | x :: xs, acc => if x == c then acc.reverse :: splitK c xs [] else splitK c xs (x :: acc)

@[expose] def toksK (l : List Char) : List (List Char) :=
  (splitK ' ' l []).filter fun t => !t.isEmpty

@[expose] def isNumK (l : List Char) : Bool := !l.isEmpty && l.all Char.isDigit

@[expose] def decK (l : List Char) : Nat := l.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

@[expose] def numK (t : List Char) : Option Nat := if isNumK t then some (decK t) else none

@[expose] def numsK : List (List Char) → Option (List Nat)
  | [] => some []
  | t :: ts => match numK t, numsK ts with
    | some n, some ns => some (n :: ns)
    | _, _ => none

@[expose] def lettersK (perms : Array (Array ℕ)) : List (List Char) → Option (List Native.Gen)
  | [] => some []
  | [t] => if t = ['x'] then some [.xi] else if t = ['t'] then some [.tau]
      else if t = ['r'] ∨ t = ['p'] ∨ t = ['g'] then some [] else none
  | [t, u] => if t = ['x'] then (lettersK perms [u]).map (.xi :: ·)
      else if t = ['t'] then (lettersK perms [u]).map (.tau :: ·)
      else if t = ['p'] then (numK u).map fun k => [.perm perms[k]!]
      else if t = ['g'] then (numK u).map fun a => [.sign a]
      else if t = ['r'] then some [] else none
  | t :: s :: a :: rest =>
    if t = ['x'] then (lettersK perms (s :: a :: rest)).map (.xi :: ·)
    else if t = ['t'] then (lettersK perms (s :: a :: rest)).map (.tau :: ·)
    else if t = ['p'] then match numK s, lettersK perms (a :: rest) with
      | some k, some w => some (.perm perms[k]! :: w)
      | _, _ => none
    else if t = ['g'] then match numK s, lettersK perms (a :: rest) with
      | some k, some w => some (.sign k :: w)
      | _, _ => none
    else if t = ['r'] then match rest with
      | [] => some []
      | d :: rest' => match numK s, numK a, numK d, lettersK perms rest' with
        | some s', some a', some d', some w => some (.rho (s' != 0, a', d') :: w)
        | _, _, _, _ => none
    else none

@[expose] def barK : List (List Char) → Option (List ℕ × List (List Char))
  | [] => some ([], [])
  | t :: rest => if t = ['|'] then some ([], rest) else match numK t, barK rest with
    | some n, some (l, w) => some (n :: l, w)
    | _, _ => none

@[expose] def lineTK (acc : Array (Array ℕ) × Array (ProdStep × List Native.Gen)) :
    List (List Char) → Option (Array (Array ℕ) × Array (ProdStep × List Native.Gen))
  | [] => some acc
  | t :: rest =>
    if t = ['P'] then (numsK rest).map fun ns => (acc.1.push ns.toArray, acc.2)
    else if t = ['E'] then match rest with
      | i :: _ => (numK i).map fun n => (acc.1, acc.2.push (.gen n, []))
      | [] => none
    else if t = ['M'] then match barK rest with
      | some (ix, w) => (lettersK acc.1 w).map fun ws => (acc.1, acc.2.push (.prod ix, ws))
      | none => none
    else if t = ['I'] then match barK rest with
      | some (ix, w) => (lettersK acc.1 w).map fun ws => (acc.1, acc.2.push (.inv ix, ws))
      | none => none
    else some acc

@[expose] def lineK (acc : Array (Array ℕ) × Array (ProdStep × List Native.Gen)) (l : List Char) :
    Option (Array (Array ℕ) × Array (ProdStep × List Native.Gen)) :=
  lineTK acc (toksK l)

@[expose] def linesK (acc : Array (Array ℕ) × Array (ProdStep × List Native.Gen)) :
    List (List Char) → Option (Array (Array ℕ) × Array (ProdStep × List Native.Gen))
  | [] => some acc
  | l :: ls => match lineK acc l with
    | some acc' => linesK acc' ls
    | none => none

@[expose] def decodeK (cs : List Char) : Option (Array (ProdStep × List Native.Gen)) :=
  (linesK (#[], #[]) (splitK '\n' cs [])).map Prod.snd

@[expose] noncomputable def stepOfC : List ℕ → ProdStep × List Native.Gen
  | 0 :: i :: _ => (.gen i, [])
  | 1 :: m :: r => (.prod (r.take m), CFSG.KC.KDenseP.decW (r.drop m))
  | 2 :: m :: r => (.inv (r.take m), CFSG.KC.KDenseP.decW (r.drop m))
  | _ => (.gen 0, [])

@[expose] noncomputable def stepsC (C : ℕ → List ℕ) (n : ℕ) : Array (ProdStep × List Native.Gen) :=
  ((List.range n).map fun k => stepOfC (C k)).toArray

@[expose] def tagEqB : ProdStep → ProdStep → Bool
  | .gen i, .gen j => i == j
  | .prod l, .prod m => l == m
  | .inv l, .inv m => l == m
  | _, _ => false

@[expose] noncomputable def stepListEqB : List (ProdStep × List Native.Gen) → List (ProdStep × List Native.Gen) → Bool
  | [], [] => true
  | s :: ss, t :: ts => tagEqB s.1 t.1 && CFSG.KC.KDenseP.wordEqB s.2 t.2 && stepListEqB ss ts
  | _, _ => false

@[expose] noncomputable def parseEqB (o : Option (Array (ProdStep × List Native.Gen)))
    (b : Array (ProdStep × List Native.Gen)) : Bool :=
  match o with
  | some a => stepListEqB a.toList b.toList
  | none => false

end CFSG.KC.NortonSLPK

end

module

public import Certificates.Data.E27.Co1S0

public section

namespace CertificateChecks.KernelCo1B.S0131301

open CFSG.Sporadic.Co1.S0 CFSG.Sporadic.Co1Schreier.Native CFSG.HardMathSupport.Foote.E27

def packR (X : Rows) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

def regsP : Array Nat := (regsM ()).map packR

def eltsP : Array Nat := (eltsM ()).map packR

def sortP : Array Nat :=
  ((List.range nS).toArray.qsort fun i k => eltsP[i]! < eltsP[k]!)

def left131P : Array Nat := (L ()).flatten

def cj131P : Array Nat := Id.run do
  let p := par
  let l := L
  let mut out : Array Nat := Array.replicate nS 0
  let mut seen : Array Bool := Array.replicate nS false
  for a in [0:nS] do
    if a != 0 && !seen[a]! && tabMul p l a (tabMul p l a a) == 0 then
      seen := seen.set! a true
      let mut queue : Array (Nat × Nat × Nat) := #[(a, 0, 0)]
      let mut qi := 0
      while qi < queue.size do
        let (x, h, hi) := queue[qi]!
        qi := qi + 1
        for j in [0:3] do
          let g := (l[j]!)[0]!
          let gv := tabMul p l g g
          let y := tabMul p l (tabMul p l g x) gv
          if !seen[y]! then
            seen := seen.set! y true
            let h' := tabMul p l g h
            let hi' := tabMul p l hi gv
            queue := queue.push (y, h', hi')
            out := out.set! y (a + (h' <<< 15) + (hi' <<< 30))
  return out

def witP : Array Nat := Id.run do
  let p := par
  let l := L
  let c := cj131P
  let mut out : Array Nat := #[]
  for a in [0:nS] do
    if a != 0 && c[a]! == 0 && tabMul p l a (tabMul p l a a) == 0 then
      let mut w := 0
      let mut k := 0
      for b in [0:nS] do
        if k < 81 && tabMul p l a b == tabMul p l b a then
          w := w ||| (b <<< (15 * k))
          k := k + 1
      out := out.push w
    else
      out := out.push 0
  return out

end CertificateChecks.KernelCo1B.S0131301

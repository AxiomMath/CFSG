module

public import Certificates.Data.Kernel.ChengHeldPropsK

public section

namespace CFSG.KC.ChengHeldP

open CFSG.OddStandard.ChengHeldData CFSG.KC.ChengHeldS2
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw

variable (n : ℕ) (m : ℕ → ℕ → ℕ) (inv g : ℕ → ℕ)

@[expose] def bitW (B x : ℕ) : Bool := decide (x < n) && B.testBit x

@[expose] def cardW (B : ℕ → Bool) : ℕ := (elemsK n B).length

@[expose] def fixW (a : ℕ → ℕ) (x : ℕ) : Bool := decide (x < n) && a x == x

@[expose] def clW (gs : List ℕ) (K : ℕ) : Bool :=
  gs.all (fun g => Nat.blt g n) &&
    Nat.beq (clStepK n m gs (clIterK n m gs K)) (clIterK n m gs K)

@[expose] def twInvsK (a : ℕ → ℕ) : List ℕ := (List.range n).filter fun s => m s (a s) == 0

@[expose] def twOrbK (a : ℕ → ℕ) (s : ℕ) : List ℕ :=
  ((List.range n).map fun x => m (m (inv x) s) (a x)).eraseDups

@[expose] def twStepK (a : ℕ → ℕ) (st : ℕ × List (List ℕ)) (s : ℕ) : ℕ × List (List ℕ) :=
  if !st.1.testBit s then
    ((twOrbK n m inv a s).foldl (fun b y => b ||| (1 <<< y)) st.1, st.2 ++ [twOrbK n m inv a s])
  else st

@[expose] def twOrbitsK (a : ℕ → ℕ) : List (List ℕ) :=
  ((twInvsK n m a).foldl (twStepK n m inv a) (0, [])).2

@[expose] def gMapW (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, y => a y
  | j + 1, y => cjK m inv y (g j)

@[expose] def orbIterW (a : ℕ → ℕ) (x : ℕ) : ℕ → ℕ
  | 0 => 1 <<< x
  | k + 1 => clStepK n (fun y j => gMapW m inv g a j y) (List.range 8) (orbIterW a x k)

@[expose] def orbW (a : ℕ → ℕ) (x K : ℕ) : Bool :=
  Nat.blt x n && (List.range 7).all (fun j => Nat.blt (g j) n) &&
    Nat.beq (clStepK n (fun y j => gMapW m inv g a j y) (List.range 8) (orbIterW n m inv g a x K))
      (orbIterW n m inv g a x K)

@[expose] def autRestW (α K : ℕ) (A : ℕ → ℕ → ℕ) : Bool :=
  let q := if α = 2 then g 0 else pwK m (g 0) 2
  let t := g 0
  let pi := g 1
  let tau := g 2
  let mlx := m (m (g 3) (g 4)) (g 6)
  ([0, 1, 2].all fun k =>
    let a := A k
    let d := autData α k
    cardW n (fixW n a) == d.1 && (twInvsK n m a).length == d.2.1 &&
      (twOrbitsK n m inv a).map List.length == d.2.2.1 &&
      ((twOrbitsK n m inv a).any fun o => o.contains 0 && o.contains q) == d.2.2.2) &&
  (let aF := A 0
   let aG := A 1
   let aU := A 2
   let cF := bitW n (clIterK n m [t, pi, m (g 3) (g 4), g 6] K)
   let cG := bitW n (clIterK n m [t, pi, tau] K)
   let cU := bitW n (clIterK n m [t, m mlx tau] K)
   if α = 2 then
     (List.range n).all (fun x => fixW n aF x == cF x) &&
       (List.range n).all (fun x => fixW n aG x == cG x) &&
       (List.range n).all (fun x => fixW n aU x == cU x) &&
       (let orbG := (twOrbitsK n m inv aG).find? fun o => o.contains 0
        match orbG with
        | some o => o.contains pi && o.contains (m q tau) && o.contains (m q (m pi tau))
        | none => false)
   else
     (List.range n).all (fun x => !fixW n aF x || cF x) &&
       (List.range n).all (fun x => !fixW n aG x || cG x) &&
       (List.range n).all (fun x => !fixW n aU x || cU x))

@[expose] def gRestW (α K : ℕ) (a : ℕ → ℕ) : Bool :=
  let t := g 0
  let pi := g 1
  let tau := g 2
  let Zt := bitW n (clIterK n m [t] K)
  let D := bitW n (clIterK n m [t, pi, tau] K)
  ((List.range n).filter fun x => Zt (m (inv x) (a x))).length == cardW n Zt &&
    (elemsK n D).all (fun x => D (a x)) &&
    (if α = 2 then
      let op := bitW n (orbIterW n m inv g a pi K)
      let ot := bitW n (orbIterW n m inv g a tau K)
      let q := t
      cardW n D == 8 && cardW n (bitW n (orbIterW n m inv g a q K)) == 1 &&
        cardW n op == 3 && op (m (m q pi) tau) && op (m q tau) &&
        cardW n ot == 3 && ot (m q pi) && ot (m pi tau) &&
        ([pi, m (m q pi) tau, m q tau, tau, m q pi, m pi tau, q].eraseDups).length == 7
    else
      let q := pwK m t 2
      let V := bitW n (clIterK n m [q, pi, m t tau] K)
      let op := bitW n (orbIterW n m inv g a pi K)
      cardW n V == 8 && (elemsK n V).all (fun x => V (a x)) && cardW n op == 6 &&
        (elemsK n V).all fun x => x == 0 || x == q || op x)

end CFSG.KC.ChengHeldP

end

module

public import Certificates.Data.CFSGNative.Fi24.Core
public import Certificates.Data.CFSGNative.Th.Tables
public import Std.Data.HashMap

public section

namespace CFSG.Sporadic.Fi24.Native

open CFSG.Sporadic.Th.Native

structure Enum where
  alpha : Table
  beta : Table
  par : Table
  lab : Table
  starts : Array Nat
deriving Inhabited

@[expose] def parRange {σ α : Type} (lo hi chunks : Nat) (setup : Unit → σ) (f : σ → Nat → α) :
    Array α :=
  let c := chunks + 1
  let per := (hi - lo + c - 1) / c
  let tasks := (List.range c).map fun t => Task.spawn fun _ =>
    let env := setup ()
    let s := lo + t * per
    let e := min hi (s + per)
    (Array.range (e - s)).map fun i => f env (s + i)
  tasks.foldl (fun acc tk => acc ++ tk.get) #[]

@[inline, expose] def getP (t : Table) (i : Nat) : Option Nat :=
  let x := t[i]!
  if x == none32 then none else some x.toNat

structure EState where
  alpha : Table
  beta : Table
  binv : Table
  par : Table
  lab : Table
  index : Std.HashMap UInt64 Nat
  next : Array (Array W)

@[inline, expose] def EState.record (st : EState) (i g : Nat) (X : Array W) (h : UInt64) :
    EState :=
  let (k, st) : Nat × EState := match st.index[h]? with
    | some k => (k, st)
    | none =>
      let k := st.alpha.size
      (k, ⟨st.alpha.push none32, st.beta.push none32, st.binv.push none32,
        st.par.push (UInt32.ofNat i), st.lab.push (UInt32.ofNat g), st.index.insert h k,
        st.next.push X⟩)
  if g = 1 then
    ⟨(st.alpha.set! i (UInt32.ofNat k)).set! k (UInt32.ofNat i), st.beta, st.binv, st.par, st.lab,
      st.index, st.next⟩
  else
    ⟨st.alpha, st.beta.set! i (UInt32.ofNat k), st.binv.set! k (UInt32.ofNat i), st.par, st.lab,
      st.index, st.next⟩

structure Gens where
  tA : Array W
  tB : Array W

@[inline, expose] def Gens.get (G : Gens) (l : Nat) : Array W := if l = 1 then G.tA else G.tB

@[expose] def enumOrbit (gens : Unit → Gens) (root : Array W) (cap batch chunks : Nat) :
    Enum := Id.run do
  let mut st : EState := ⟨#[none32], #[none32], #[none32], #[0], #[0],
    (∅ : Std.HashMap UInt64 Nat).insert (hashRows root) 0, #[]⟩
  let mut cur : Array (Array W) := #[root]
  let mut lo := 0
  let mut starts : Array Nat := #[0]
  for _ in [0:cap] do
    if cur.size = 0 then break
    let hi := lo + cur.size
    starts := starts.push hi
    let nb := (cur.size + batch - 1) / batch
    for b in [0:nb] do
      let s := lo + b * batch
      let e := min hi (s + batch)
      let al := st.alpha
      let bi := st.binv
      let cr := cur
      let imgs := parRange s e chunks gens fun G i =>
        let X := cr[i - lo]!
        let ia := if (getP al i).isSome then none else
          let Y := (stepForm G.tA X).rows
          some (Y, hashRows Y)
        let ib := match getP bi i with
          | some p => if (getP bi p).isSome then none else
              let Y := (stepForm G.tB X).rows
              some (Y, hashRows Y)
          | none =>
              let Y := (stepForm G.tB X).rows
              some (Y, hashRows Y)
        (ia, ib)
      for i in [s:e] do
        let (ia, ib) := imgs[i - s]!
        if (getP st.alpha i).isNone then
          match ia with
          | some (Y, h) => st := st.record i 1 Y h
          | none => pure ()
        let derived := match getP st.binv i with
          | some p => getP st.binv p
          | none => none
        match derived with
        | some q => st := ⟨st.alpha, st.beta.set! i (UInt32.ofNat q), st.binv, st.par, st.lab,
            st.index, st.next⟩
        | none =>
          match ib with
          | some (Y, h) => st := st.record i 2 Y h
          | none => pure ()
    lo := hi
    cur := st.next
    st := ⟨st.alpha, st.beta, st.binv, st.par, st.lab, st.index, #[]⟩
  return ⟨st.alpha, st.beta, st.par, st.lab, starts⟩

end CFSG.Sporadic.Fi24.Native

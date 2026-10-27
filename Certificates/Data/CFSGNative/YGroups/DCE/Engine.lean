module

public import Certificates.Data.CFSGNative.YGroups.DCE.Omega

public section

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[inline, expose] def pcomp (t u : Array Nat) : Array Nat := u.map fun x => t[x]!

structure Ctx where
  n : Nat
  letters : Array (Array Nat)
  cl : Nat
  D : XData
  nodes : Array (Nat × Nat)
  discover : Bool
  one : Array Nat

@[expose] def Ctx.c (C : Ctx) : Array Nat := C.letters[C.cl]!

@[expose] def Ctx.nodeOK (C : Ctx) (j i p : Nat) : Bool :=
  C.discover || C.nodes[j]? == some (i, p)

structure CF where
  i : Nat
  p : Nat
  k : Nat
  a : Array Nat

structure Rules (C : Ctx) (PE : Array Nat → Prop) (W : Nat → Array Nat → Prop)
    (V : Nat → Nat → Nat → Array Nat → Prop) : Prop where
  letter : ∀ l < C.letters.size, PE C.letters[l]!
  mul : ∀ a b, PE a → PE b → PE (pcomp a b)
  inv : ∀ a, PE a → isInvA C.n a (invCand C.n a) = true → PE (invCand C.n a)
  wpe : ∀ j a, W j a → PE a
  wroot : ∀ a, PE a → W 0 a
  wmul : ∀ j a b, W j a → W j b → W j (pcomp a b)
  winv : ∀ j a, W j a → isInvA C.n a (invCand C.n a) = true → W j (invCand C.n a)
  wid : ∀ j, W j C.one
  r0 : ∀ j i p, 0 < j → C.nodeOK j i p = true → p < C.D.N → V i p j (idA C.n)
  r1 : ∀ i p k a, V i p k a → isInvA C.n a (invCand C.n a) = true →
    V k (act C.D a p) i (invCand C.n a)
  r2 : ∀ j p k a s q, V j p k a → W j s → q < C.D.N → act C.D s q = p →
    V j q k (pcomp a s)
  r3 : ∀ i p k a b, V i p k a → V i p k b → isInvA C.n b (invCand C.n b) = true →
    W k (pcomp a (invCand C.n b))
  r4 : ∀ g i j k a b, PE g → isInvA C.n g (invCand C.n g) = true →
    V i (act C.D g 0) j a → V j (act C.D a (act C.D (pcomp g C.c) 0)) k b →
    V i (act C.D (pcomp g C.c) 0) k
      (pcomp (pcomp b a) (pcomp (pcomp g C.c) (invCand C.n g)))
  r5 : ∀ g i j k a b, PE g → isInvA C.n g (invCand C.n g) = true →
    isInvA C.n a (invCand C.n a) = true →
    V i (act C.D g 0) j a → V i (act C.D (pcomp g C.c) 0) k b →
    V j (act C.D a (act C.D (pcomp g C.c) 0)) k
      (pcomp (pcomp b (pcomp (pcomp g C.c) (invCand C.n g))) (invCand C.n a))

structure Env where
  C : Ctx
  PE : Array Nat → Prop
  W : Nat → Array Nat → Prop
  V : Nat → Nat → Nat → Array Nat → Prop
  rules : Rules C PE W V

abbrev PElt (E : Env) : Type := {a : Array Nat // E.PE a}

abbrev WElt (E : Env) : Type := {x : Nat × Array Nat // E.W x.1 x.2}

abbrev VElt (E : Env) : Type := {f : CF // E.V f.i f.p f.k f.a}

namespace Env

variable (E : Env)

@[expose] def pid : PElt E := ⟨E.C.one, E.rules.wpe 0 _ (E.rules.wid 0)⟩

instance : Inhabited (PElt E) := ⟨E.pid⟩

@[expose] def wid (j : Nat) : WElt E := ⟨(j, E.C.one), E.rules.wid j⟩

instance : Inhabited (WElt E) := ⟨E.wid 0⟩

@[expose] def pletter (l : Nat) : PElt E :=
  if h : l < E.C.letters.size then ⟨E.C.letters[l]!, E.rules.letter l h⟩ else E.pid

@[inline, expose] def pmul (x y : PElt E) : PElt E :=
  ⟨pcomp x.1 y.1, E.rules.mul _ _ x.2 y.2⟩

@[expose] def pinv (x : PElt E) : PElt E :=
  if h : isInvA E.C.n x.1 (invCand E.C.n x.1) = true then ⟨_, E.rules.inv _ x.2 h⟩ else x

@[inline, expose] def wmul (x y : WElt E) : WElt E :=
  if h : x.1.1 = y.1.1 then
    ⟨(x.1.1, pcomp x.1.2 y.1.2), E.rules.wmul _ _ _ x.2 (by rw [h]; exact y.2)⟩
  else x

@[expose] def winv (x : WElt E) : WElt E :=
  if h : isInvA E.C.n x.1.2 (invCand E.C.n x.1.2) = true then
    ⟨(x.1.1, invCand E.C.n x.1.2), E.rules.winv _ _ x.2 h⟩
  else x

@[inline, expose] def wpe (x : WElt E) : PElt E := ⟨x.1.2, E.rules.wpe _ _ x.2⟩

@[inline, expose] def wroot (x : PElt E) : WElt E := ⟨(0, x.1), E.rules.wroot _ x.2⟩

@[expose] def mk0 (j i p : Nat) : Option (VElt E) :=
  if h : 0 < j ∧ E.C.nodeOK j i p = true ∧ p < E.C.D.N then
    some ⟨⟨i, p, j, idA E.C.n⟩, E.rules.r0 j i p h.1 h.2.1 h.2.2⟩
  else none

@[expose] def mk1 (f : VElt E) : Option (VElt E) :=
  if h : isInvA E.C.n f.1.a (invCand E.C.n f.1.a) = true then
    some ⟨⟨f.1.k, act E.C.D f.1.a f.1.p, f.1.i, invCand E.C.n f.1.a⟩,
      E.rules.r1 _ _ _ _ f.2 h⟩
  else none

@[expose] def mk2 (f : VElt E) (s : WElt E) (q : Nat) : Option (VElt E) :=
  if h : s.1.1 = f.1.i ∧ q < E.C.D.N ∧ act E.C.D s.1.2 q = f.1.p then
    some ⟨⟨f.1.i, q, f.1.k, pcomp f.1.a s.1.2⟩,
      E.rules.r2 _ _ _ _ _ _ f.2 (by rw [← h.1]; exact s.2) h.2.1 h.2.2⟩
  else none

@[expose] def mk3 (f g : VElt E) : Option (WElt E) :=
  if h : f.1.i = g.1.i ∧ f.1.p = g.1.p ∧ f.1.k = g.1.k ∧
      isInvA E.C.n g.1.a (invCand E.C.n g.1.a) = true then
    some ⟨(f.1.k, pcomp f.1.a (invCand E.C.n g.1.a)),
      E.rules.r3 f.1.i f.1.p f.1.k f.1.a g.1.a f.2
        (by rw [h.1, h.2.1, h.2.2.1]; exact g.2) h.2.2.2⟩
  else none

@[inline, expose] def conjC (g : PElt E) : Array Nat :=
  pcomp (pcomp g.1 E.C.c) (invCand E.C.n g.1)

@[expose] def mk4 (g : PElt E) (f f2 : VElt E) : Option (VElt E) :=
  if h : isInvA E.C.n g.1 (invCand E.C.n g.1) = true ∧ f.1.p = act E.C.D g.1 0 ∧
      f2.1.i = f.1.k ∧ f2.1.p = act E.C.D f.1.a (act E.C.D (pcomp g.1 E.C.c) 0) then
    some ⟨⟨f.1.i, act E.C.D (pcomp g.1 E.C.c) 0, f2.1.k,
        pcomp (pcomp f2.1.a f.1.a) (E.conjC g)⟩,
      E.rules.r4 g.1 f.1.i f.1.k f2.1.k f.1.a f2.1.a g.2 h.1 (by rw [← h.2.1]; exact f.2)
        (by rw [← h.2.2.1, ← h.2.2.2]; exact f2.2)⟩
  else none

@[expose] def mk5 (g : PElt E) (f f3 : VElt E) : Option (VElt E) :=
  if h : isInvA E.C.n g.1 (invCand E.C.n g.1) = true ∧
      isInvA E.C.n f.1.a (invCand E.C.n f.1.a) = true ∧ f.1.p = act E.C.D g.1 0 ∧
      f3.1.i = f.1.i ∧ f3.1.p = act E.C.D (pcomp g.1 E.C.c) 0 then
    some ⟨⟨f.1.k, act E.C.D f.1.a (act E.C.D (pcomp g.1 E.C.c) 0), f3.1.k,
        pcomp (pcomp f3.1.a (E.conjC g)) (invCand E.C.n f.1.a)⟩,
      E.rules.r5 g.1 f.1.i f.1.k f3.1.k f.1.a f3.1.a g.2 h.1 h.2.1
        (by rw [← h.2.2.1]; exact f.2) (by rw [← h.2.2.2.1, ← h.2.2.2.2]; exact f3.2)⟩
  else none

end Env

@[expose] def firstMoved (n : Nat) (σ : Array Nat) : Nat := Id.run do
  for x in [0:n] do
    if σ[x]! != x then return x
  return n

@[inline, expose] def isIdA (n : Nat) (σ : Array Nat) : Bool := allLt n fun x => σ[x]! == x

@[inline, expose] def xorshift (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

structure Lv (E : Env) where
  β : Nat
  sg : Array (WElt E)
  si : Array (WElt E)
  pts : Array Nat
  pos : Array Nat
  tp : Array Nat
  tl : Array Nat

structure Bsgs (E : Env) where
  lv : Array (Lv E)

instance (E : Env) : Inhabited (Bsgs E) := ⟨{ lv := #[] }⟩

instance (E : Env) : Inhabited (Lv E) :=
  ⟨{ β := 0, sg := #[], si := #[], pts := #[], pos := #[], tp := #[], tl := #[] }⟩

@[expose] def lvOrbit (n β : Nat) (sg : Array (Array Nat)) :
    Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let mut pos : Array Nat := (Array.replicate n n).set! β 0
  let mut tp : Array Nat := Array.replicate n n
  let mut tl : Array Nat := Array.replicate n 0
  let mut pts : Array Nat := #[β]
  let mut h := 0
  for _ in [0:n] do
    if h < pts.size then
      let x := pts[h]!
      h := h + 1
      for i in [0:sg.size] do
        let y := sg[i]![x]!
        if pos[y]! == n then
          pos := pos.set! y pts.size
          tp := tp.set! y x
          tl := tl.set! y i
          pts := pts.push y
    else
      break
  return (pts, pos, tp, tl)

namespace Env

variable (E : Env)

@[expose] def mkLv (β : Nat) (sg : Array (WElt E)) : Lv E :=
  let (pts, pos, tp, tl) := lvOrbit E.C.n β (sg.map (·.1.2))
  { β, sg, si := sg.map E.winv, pts, pos, tp, tl }

@[expose] def lvTrans (j : Nat) (L : Lv E) (x : Nat) : WElt E := Id.run do
  if x == L.β then return E.wid j
  let mut u := L.sg[L.tl[x]!]!
  let mut c := L.tp[x]!
  for _ in [0:E.C.n] do
    if c == L.β then break
    u := E.wmul u L.sg[L.tl[c]!]!
    c := L.tp[c]!
  return u

@[expose] def sift (B : Bsgs E) (σ : WElt E) : Nat × WElt E := Id.run do
  let n := E.C.n
  let mut g := σ
  for l in [0:B.lv.size] do
    let L := B.lv[l]!
    let b := g.1.2[L.β]!
    if L.pos[b]! == n then return (l, g)
    let mut c := b
    for _ in [0:n] do
      if c == L.β then break
      g := E.wmul L.si[L.tl[c]!]! g
      c := L.tp[c]!
  return (B.lv.size, g)

@[expose] def member (B : Bsgs E) (σ : WElt E) : Bool :=
  let (l, r) := E.sift B σ
  l == B.lv.size && isIdA E.C.n r.1.2

@[expose] def memberFast (B : Bsgs E) (σ : Array Nat) : Bool := Id.run do
  let n := E.C.n
  let mut w : Array (Nat × Nat) := #[]
  for l in [0:B.lv.size] do
    let L := B.lv[l]!
    let mut b := σ[L.β]!
    for (l', i) in w do
      b := (B.lv[l']!.si[i]!).1.2[b]!
    if L.pos[b]! == n then return false
    let mut c := b
    for _ in [0:n] do
      if c == L.β then break
      let i := L.tl[c]!
      w := w.push (l, i)
      c := L.tp[c]!
  let mut x := 1
  for _ in [0:24] do
    x := (x * 1103 + 7) % n
    let mut y := σ[x]!
    for (l', i) in w do
      y := (B.lv[l']!.si[i]!).1.2[y]!
    if y != x then return false
  return true

@[expose] def addStrong (B : Bsgs E) (l : Nat) (r : WElt E) : Bsgs E := Id.run do
  let n := E.C.n
  let mut lv := B.lv
  if lv.size ≤ l then
    let β := firstMoved n r.1.2
    if β == n then return B
    lv := lv.push (E.mkLv β #[])
  let top := min l (lv.size - 1)
  for l' in [0:top + 1] do
    lv := lv.modify l' fun L => E.mkLv L.β (L.sg.push r)
  return { lv }

@[expose] def close (j : Nat) (B : Bsgs E) (rng : UInt64) (tries fuel : Nat) :
    Bsgs E × UInt64 := Id.run do
  let n := E.C.n
  let mut B := B
  let mut rng := rng
  let mut ok := 0
  for _ in [0:fuel] do
    if tries ≤ ok || B.lv.size == 0 then break
    rng := xorshift rng
    let l := (rng.toNat >>> 7) % B.lv.size
    let L := B.lv[l]!
    if L.sg.size == 0 then
      ok := ok + 1
      continue
    rng := xorshift rng
    let x := L.pts[(rng.toNat >>> 7) % L.pts.size]!
    rng := xorshift rng
    let i := (rng.toNat >>> 7) % L.sg.size
    let s := L.sg[i]!
    let y := s.1.2[x]!
    let sch := E.wmul (E.winv (E.lvTrans j L y)) (E.wmul s (E.lvTrans j L x))
    if E.memberFast B sch.1.2 then
      ok := ok + 1
    else
      let (l2, r) := E.sift B sch
      if l2 == B.lv.size && isIdA n r.1.2 then
        ok := ok + 1
      else
        B := E.addStrong B l2 r
        ok := 0
  return (B, rng)

@[expose] def bsAdd (j : Nat) (B : Bsgs E) (σ : WElt E) (rng : UInt64) : Bsgs E × UInt64 :=
  let (l, r) := E.sift B σ
  if l == B.lv.size && isIdA E.C.n r.1.2 then (B, rng)
  else E.close j (E.addStrong B l r) rng 40 200000

@[expose] def bsOrder (B : Bsgs E) : Nat := B.lv.foldl (fun a L => a * L.pts.size) 1

end Env

@[expose] def omegaOrbits (N : Nat) (gO : Array (Array Nat)) :
    Array Nat × Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let mut orb : Array Nat := Array.replicate N N
  let mut spar : Array Nat := Array.replicate N N
  let mut sgen : Array Nat := Array.replicate N 0
  let mut dep : Array Nat := Array.replicate N 0
  let mut reps : Array Nat := #[]
  let mut queue : Array Nat := Array.mkEmpty N
  for s in [0:N] do
    if orb[s]! == N then
      let k := reps.size
      reps := reps.push s
      orb := orb.set! s k
      let mut h := queue.size
      queue := queue.push s
      for _ in [0:N] do
        if h < queue.size then
          let x := queue[h]!
          h := h + 1
          for gi in [0:gO.size] do
            let y := gO[gi]![x]!
            if y < N && orb[y]! == N then
              orb := orb.set! y k
              spar := spar.set! y x
              sgen := sgen.set! y gi
              dep := dep.set! y (dep[x]! + 1)
              queue := queue.push y
        else
          break
  return (orb, spar, sgen, dep, reps)

inductive Work (E : Env) where
  | entry (f : VElt E)
  | grow (s : WElt E)

structure St (E : Env) where
  nodes : Array (Nat × Nat)
  gens : Array (Array (WElt E))
  gO : Array (Array (Array Nat))
  orb : Array (Array Nat)
  spar : Array (Array Nat)
  sgen : Array (Array Nat)
  dep : Array (Array Nat)
  reps : Array (Array Nat)
  tab : Array (Array (Option (VElt E)))
  bs : Array (Bsgs E)
  prs : Array (Array (Option (Array Nat)))
  done : Array (Array Bool)
  work : Array (Work E)
  err : Nat
  prog : Nat
  rng : UInt64
  nbr : Array Nat
  nbrLoc : Std.HashMap Nat Nat
  hN : Array (PElt E)
  scans : Nat

@[inline, expose] def St.setTab {E : Env} (st : St E) (j o : Nat) (v : Option (VElt E)) : St E :=
  let tab := st.tab
  let st := { st with tab := #[] }
  { st with tab := tab.modify j (·.set! o v) }

@[inline, expose] def St.pushWork {E : Env} (st : St E) (w : Work E) : St E :=
  let work := st.work
  let st := { st with work := #[] }
  { st with work := work.push w }

@[inline, expose] def St.popWork {E : Env} (st : St E) : St E :=
  let work := st.work
  let st := { st with work := #[] }
  { st with work := work.pop }

@[inline, expose] def St.setPrs {E : Env} (st : St E) (i o : Nat) (l : Array Nat) : St E :=
  let prs := st.prs
  let st := { st with prs := #[] }
  { st with prs := prs.modify i (·.set! o (some l)) }

@[inline, expose] def St.setDone {E : Env} (st : St E) (i o : Nat) : St E :=
  let done := st.done
  let st := { st with done := #[] }
  { st with done := done.modify i (·.set! o true) }

namespace Env

variable (E : Env)

@[expose] def omegaPerm (σ : Array Nat) : Array Nat :=
  let N := E.C.D.N
  let chunks := 8
  let sz := N / chunks + 1
  let parts := (List.range chunks).map fun c => Task.spawn fun _ => Id.run do
    let mut out : Array Nat := Array.mkEmpty sz
    for k in [0:sz] do
      let x := c * sz + k
      if x < N then out := out.push (act E.C.D σ x)
    return out
  parts.foldl (fun acc t => acc ++ t.get) (Array.mkEmpty N)

@[expose] def transport (st : St E) (j x : Nat) : WElt E := Id.run do
  let N := E.C.D.N
  let spar := st.spar[j]!
  let sgen := st.sgen[j]!
  let gens := st.gens[j]!
  let p0 := spar[x]!
  if p0 == N then return E.wid j
  let mut s := gens[sgen[x]!]!
  let mut c := p0
  for _ in [0:N] do
    let pc := spar[c]!
    if pc == N then break
    s := E.wmul s gens[sgen[c]!]!
    c := pc
  return s

@[expose] def omegaTrans (st : St E) (x : Nat) : PElt E := E.wpe (E.transport st 0 x)

@[expose] def factAt (st : St E) (j y : Nat) : Option (VElt E) :=
  match st.tab[j]![st.orb[j]![y]!]! with
  | none => none
  | some f => E.mk2 f (E.winv (E.transport st j y)) y

@[expose] def setEntry (st : St E) (f : VElt E) : St E :=
  let j := f.1.i
  if st.nodes.size ≤ j then { st with err := 1 } else
  let o := st.orb[j]![f.1.p]!
  let r := st.reps[j]![o]!
  match E.mk2 f (E.transport st j f.1.p) r with
  | none => { st with err := 2 }
  | some f' =>
    match st.tab[j]![o]! with
    | none =>
      let st := (st.setTab j o (some f'))
      let st := { st with prog := st.prog + 1 }
      match E.mk1 f' with
      | some g => st.pushWork (.entry g)
      | none => { st with err := 3 }
    | some e =>
      if e.1.k == f'.1.k then
        match E.mk3 e f' with
        | some w => if isIdA E.C.n w.1.2 then st else st.pushWork (.grow w)
        | none => { st with err := 4 }
      else { st with err := 5 }

@[expose] def composeO (a b : Array Nat) : Array Nat := b.map fun x => a[x]!

@[expose] def maxEntry (a : Array Nat) : Nat := a.foldl max 0

@[expose] def growMany (st : St E) (k : Nat) (ws : Array (WElt E)) : St E := Id.run do
  if k == 0 || st.nodes.size ≤ k then return st
  let mut st := st
  let mut bs := st.bs[k]!
  let mut rng := st.rng
  let mut added : Array (WElt E) := #[]
  for w in ws do
    if w.1.1 == k && !(E.memberFast bs w.1.2) then
      let (bs', rng') := E.bsAdd k bs w rng
      bs := bs'
      rng := rng'
      added := added.push w
  if added.size == 0 then return { st with rng }
  let mut gk := st.gens[k]! ++ added
  let mut gOk := st.gO[k]! ++ added.map fun w => E.omegaPerm w.1.2
  let mut res := omegaOrbits E.C.D.N gOk
  for _ in [0:6] do
    if maxEntry res.2.2.2.1 ≤ 8 then break
    for _ in [0:3] do
      rng := xorshift rng
      let mut w := gk[(rng.toNat >>> 7) % gk.size]!
      let mut wO := gOk[(rng.toNat >>> 7) % gk.size]!
      for _ in [0:5] do
        rng := xorshift rng
        let a := (rng.toNat >>> 7) % gk.size
        w := E.wmul w gk[a]!
        wO := composeO wO gOk[a]!
      gk := gk.push w
      gOk := gOk.push wO
    res := omegaOrbits E.C.D.N gOk
  let (orb, spar, sgen, dep, reps) := res
  let oldTab := st.tab[k]!
  let oldReps := st.reps[k]!
  let oldDone := st.done[k]!
  let mut newDone : Array Bool := Array.replicate reps.size false
  for o in [0:oldReps.size] do
    if oldDone[o]! then
      newDone := newDone.set! orb[oldReps[o]!]! true
  st := { st with
    gens := st.gens.set! k gk, gO := st.gO.set! k gOk, orb := st.orb.set! k orb,
    spar := st.spar.set! k spar, sgen := st.sgen.set! k sgen, dep := st.dep.set! k dep,
    reps := st.reps.set! k reps, tab := st.tab.set! k (Array.replicate reps.size none),
    bs := st.bs.set! k bs, prs := st.prs.set! k (Array.replicate reps.size none),
    done := st.done.set! k newDone, rng, prog := st.prog + 1 }
  for o in [0:oldTab.size] do
    match oldTab[o]! with
    | none => pure ()
    | some e =>
      let rOld := oldReps[o]!
      let o' := st.orb[k]![rOld]!
      let r' := st.reps[k]![o']!
      match E.mk2 e (E.transport st k rOld) r' with
      | none => st := { st with err := 6 }
      | some e' =>
        match st.tab[k]![o']! with
        | none => st := st.setTab k o' (some e')
        | some e2 =>
          if e2.1.k == e'.1.k then
            match E.mk3 e2 e' with
            | some w => if !(isIdA E.C.n w.1.2) then st := st.pushWork (.grow w)
            | none => st := { st with err := 7 }
          else st := { st with err := 8 }
  return st

@[expose] def process (st : St E) (fuel : Nat) : St E := Id.run do
  let mut st := st
  let mut pend : Array (Array (WElt E)) := Array.replicate st.nodes.size #[]
  for _ in [0:fuel] do
    if st.err != 0 then break
    match st.work.back? with
    | none =>
      let mut k := pend.size
      for j in [0:pend.size] do
        if k == pend.size && pend[j]!.size != 0 then k := j
      if k == pend.size then break
      let ws := pend[k]!
      pend := pend.set! k #[]
      st := E.growMany st k ws
      if pend.size < st.nodes.size then
        pend := pend ++ Array.replicate (st.nodes.size - pend.size) #[]
    | some w =>
      st := st.popWork
      match w with
      | .entry f => st := E.setEntry st f
      | .grow s =>
        if s.1.1 < pend.size then pend := pend.modify s.1.1 (·.push s)
  return st

@[expose] def stabElts (st : St E) (i r K : Nat) (rng : UInt64) : Array (WElt E) × UInt64 :=
  Id.run do
  let N := E.C.D.N
  let gens := st.gens[i]!
  let gO := st.gO[i]!
  let orb := st.orb[i]!
  let mut rng := rng
  let mut out : Array (WElt E) := #[]
  if gens.size == 0 then return (out, rng)
  let o := orb[r]!
  for _ in [0:K] do
    let mut x := r
    rng := xorshift rng
    let steps := (rng.toNat >>> 7) % 40
    for _ in [0:steps] do
      rng := xorshift rng
      x := gO[(rng.toNat >>> 7) % gO.size]![x]!
    rng := xorshift rng
    let gi := (rng.toNat >>> 7) % gens.size
    let y := gO[gi]![x]!
    if y < N && orb[y]! == o && orb[x]! == o then
      let ux := E.transport st i x
      let uy := E.transport st i y
      let ur := E.transport st i r
      let a := E.wmul (E.winv uy) (E.wmul gens[gi]! ux)
      out := out.push (E.wmul ur (E.wmul a (E.winv ur)))
  return (out, rng)

@[expose] def pairReps (st : St E) (i o : Nat) (g0 : PElt E) (rng : UInt64) :
    Array Nat × UInt64 := Id.run do
  let N := E.C.D.N
  let r := st.reps[i]![o]!
  let (ys, rng) := E.stabElts st i r 4 rng
  let g0i := invCand E.C.n g0.1
  let ys' := ys.map fun y => pcomp g0i (pcomp y.1.2 g0.1)
  let nbr := st.nbr
  let loc := st.nbrLoc
  let mut seen : Array Bool := Array.replicate nbr.size false
  let mut out : Array Nat := #[]
  for t in [0:nbr.size] do
    if !seen[t]! then
      out := out.push t
      seen := seen.set! t true
      let mut queue : Array Nat := #[t]
      let mut h := 0
      for _ in [0:nbr.size] do
        if h < queue.size then
          let u := queue[h]!
          h := h + 1
          for y in ys' do
            let v := act E.C.D y nbr[u]!
            match loc.get? v with
            | some w =>
              if !seen[w]! then
                seen := seen.set! w true
                queue := queue.push w
            | none => pure ()
        else
          break
  let _ := N
  return (out, rng)

@[expose] def scan (st : St E) (i o ν : Nat) (g0 : PElt E) : St E × Bool :=
  match st.tab[i]![o]! with
  | none => (st, true)
  | some f =>
    let g := E.pmul g0 st.hN[ν]!
    let gc := pcomp g.1 E.C.c
    let q := act E.C.D gc 0
    let y := act E.C.D f.1.a q
    let st := { st with scans := st.scans + 1 }
    match E.factAt st f.1.k y with
    | some f2 =>
      match E.mk4 g f f2 with
      | some nf => (E.setEntry st nf, false)
      | none => ({ st with err := 9 }, false)
    | none =>
      match E.factAt st i q with
      | some f3 =>
        match E.mk5 g f f3 with
        | some nf => (E.setEntry st nf, false)
        | none => ({ st with err := 10 }, false)
      | none => (st, true)

@[expose] def scanPass (st : St E) : St E := Id.run do
  let mut st := st
  for i in [0:st.nodes.size] do
    let mut o := 0
    for _ in [0:E.C.D.N + 1] do
      if st.err != 0 || st.reps[i]!.size ≤ o then break
      if st.done[i]![o]! then
        o := o + 1
        continue
      match st.tab[i]![o]! with
      | none => pure ()
      | some f =>
        let g0 := E.omegaTrans st f.1.p
        let lst ← match st.prs[i]![o]! with
          | some l => pure l
          | none => do
            let (l, rng) := E.pairReps st i o g0 st.rng
            st := { st with rng }
            pure l
        let mut blocked : Array Nat := #[]
        let mut aborted := false
        for ν in lst do
          if st.err != 0 then break
          if st.reps[i]!.size ≤ o then
            aborted := true
            break
          match st.tab[i]![o]! with
          | none =>
            aborted := true
            break
          | some f' =>
            if f'.1.p != f.1.p then
              aborted := true
              break
            let (st', b) := E.scan st i o ν g0
            st := E.process st' 100000000
            if b then blocked := blocked.push ν
        if !aborted && o < st.reps[i]!.size then
          match st.tab[i]![o]! with
          | some f' =>
            if f'.1.p == f.1.p then
              if blocked.size == 0 then st := st.setDone i o
              else st := st.setPrs i o blocked
          | none => pure ()
      o := o + 1
  return st

@[expose] def addNode (st : St E) (i p : Nat) : St E :=
  let N := E.C.D.N
  let (orb, spar, sgen, dep, reps) := omegaOrbits N #[]
  { st with
    nodes := st.nodes.push (i, p), gens := st.gens.push #[], gO := st.gO.push #[],
    orb := st.orb.push orb, spar := st.spar.push spar, sgen := st.sgen.push sgen,
    dep := st.dep.push dep, reps := st.reps.push reps,
    tab := st.tab.push (Array.replicate reps.size none), bs := st.bs.push { lv := #[] },
    prs := st.prs.push (Array.replicate reps.size none),
    done := st.done.push (Array.replicate reps.size false) }

@[expose] def newNode (st : St E) (i o : Nat) : St E := Id.run do
  let r := st.reps[i]![o]!
  let j := st.nodes.size
  match E.mk0 j i r with
  | none => return { st with err := 11 }
  | some f0 =>
    let mut st := E.addNode st i r
    let (ys, rng) := E.stabElts st i r 30 st.rng
    st := { st with rng }
    let mut ws : Array (WElt E) := #[]
    for y in ys do
      match E.mk2 f0 y r with
      | some f1 =>
        match E.mk3 f0 f1 with
        | some w => ws := ws.push w
        | none => pure ()
      | none => pure ()
    st := E.growMany st j ws
    st := E.setEntry st f0
    st := E.process st 100000000
    return st

@[expose] def init : St E := Id.run do
  let D := E.C.D
  let N := D.N
  let L := E.C.letters.size
  let mut gens0 : Array (WElt E) := (Array.range L).map fun l => E.wroot (E.pletter l)
  let mut gO0 := gens0.map fun w => E.omegaPerm w.1.2
  let mut res := omegaOrbits N gO0
  let mut rng : UInt64 := 0x9E3779B97F4A7C15
  for _ in [0:40] do
    if maxEntry res.2.2.2.1 ≤ 8 then break
    let mut w := gens0[0]!
    let mut wO := gO0[0]!
    for _ in [0:8] do
      rng := xorshift rng
      let a := (rng.toNat >>> 7) % gens0.size
      w := E.wmul w gens0[a]!
      wO := composeO wO gO0[a]!
    gens0 := gens0.push w
    gO0 := gO0.push wO
    res := omegaOrbits N gO0
  let (orb, spar, sgen, dep, reps) := res
  let q1 := act D E.C.c 0
  let fixL := (List.range L).filter fun l => l != E.C.cl
  let mut nbr : Array Nat := #[q1]
  let mut hN : Array (PElt E) := #[E.pid]
  let mut loc : Std.HashMap Nat Nat := ({} : Std.HashMap Nat Nat).insert q1 0
  let mut h := 0
  for _ in [0:N] do
    if h < nbr.size then
      let x := nbr[h]!
      let hx := hN[h]!
      h := h + 1
      for l in fixL do
        let y := act D (E.C.letters[l]!) x
        if !(loc.contains y) then
          loc := loc.insert y nbr.size
          nbr := nbr.push y
          hN := hN.push (E.pmul (E.pletter l) hx)
    else
      break
  return {
    nodes := #[(0, 0)], gens := #[gens0], gO := #[gO0], orb := #[orb], spar := #[spar],
    sgen := #[sgen], dep := #[dep], reps := #[reps], tab := #[Array.replicate reps.size none],
    bs := #[{ lv := #[] }], prs := #[Array.replicate reps.size none],
    done := #[Array.replicate reps.size false], work := #[], err := 0,
    prog := 0, rng, nbr, nbrLoc := loc, hN, scans := 0 }

@[expose] def firstOpen (st : St E) : Option (Nat × Nat) := Id.run do
  for i in [0:st.nodes.size] do
    let t := st.tab[i]!
    for o in [0:t.size] do
      if t[o]!.isNone then return some (i, o)
  return none

@[expose] def finish (st : St E) : St E := Id.run do
  let mut st := st
  let mut bs : Bsgs E := { lv := #[] }
  let mut rng := st.rng
  for w in st.gens[0]! do
    let (bs', rng') := E.bsAdd 0 bs w rng
    bs := bs'
    rng := rng'
  st := { st with bs := st.bs.set! 0 bs, rng }
  for j in [0:st.nodes.size] do
    let (bs', rng') := E.close j st.bs[j]! st.rng 400 2000000
    st := { st with bs := st.bs.set! j bs', rng := rng' }
  return st

@[expose] def run (fuel : Nat) : St E := Id.run do
  let mut st := E.init
  st := E.newNode st 0 0
  for _ in [0:fuel] do
    if st.err != 0 then break
    for _ in [0:1000] do
      let before := st.prog
      st := E.scanPass st
      if st.err != 0 || st.prog == before then break
    if st.err != 0 then break
    match E.firstOpen st with
    | none => break
    | some (i, o) => st := E.newNode st i o
  return E.finish st

@[expose] def levelOK (j l : Nat) (lv : Array (Lv E)) : Bool :=
  let n := E.C.n
  let L := lv[l]!
  decide (L.β < n) && L.pos.size == n && L.pts.size != 0 && L.pts[0]! == L.β &&
    L.sg.all (fun s => s.1.1 == j && allLt l fun m => s.1.2[lv[m]!.β]! == lv[m]!.β) &&
    allLt L.pts.size fun t =>
      let x := L.pts[t]!
      decide (x < n) && L.pos[x]! == t &&
        (t == 0 || (decide (L.tl[x]! < L.sg.size) && decide (L.tp[x]! < n) &&
          decide (L.pos[L.tp[x]!]! < t) && L.pts[L.pos[L.tp[x]!]!]! == L.tp[x]! &&
            (L.sg[L.tl[x]!]!).1.2[L.tp[x]!]! == x))

@[expose] def chainBound (st : St E) (j : Nat) : Nat :=
  st.bs[j]!.lv.foldl (fun a L => a * L.pts.size) 1

@[expose] def nodeClosed (st : St E) (j : Nat) : Bool :=
  let N := E.C.D.N
  let nn := st.nodes.size
  let gens := st.gens[j]!
  let spar := st.spar[j]!
  let sgen := st.sgen[j]!
  let dep := st.dep[j]!
  gens.all (fun w => w.1.1 == j) &&
    allLt N fun x =>
      let px := spar[x]!
      if px == N then
        match st.tab[j]![st.orb[j]![x]!]! with
        | some f => f.1.i == j && f.1.p == x && decide (f.1.k < nn)
        | none => false
      else
        decide (px < N) && decide (dep[px]! < dep[x]!) && decide (sgen[x]! < gens.size) &&
          act E.C.D (gens[sgen[x]!]!).1.2 px == x

@[expose] def countIndex (st : St E) (ord : Nat) : Nat :=
  (List.range st.nodes.size).foldl (fun a j => a + ord / E.chainBound st j) 0

@[expose] def outOK (st : St E) (ord bound : Nat) : Bool :=
  let nn := st.nodes.size
  st.err == 0 && decide (0 < nn) && st.gens.size == nn && st.spar.size == nn &&
    st.sgen.size == nn && st.dep.size == nn && st.orb.size == nn && st.tab.size == nn &&
    st.bs.size == nn &&
    allLt nn (fun j => E.nodeClosed st j &&
      allLt st.bs[j]!.lv.size fun l => E.levelOK j l st.bs[j]!.lv) &&
    decide (E.countIndex st ord ≤ bound)

end Env

end CFSG.YGroups.DCE

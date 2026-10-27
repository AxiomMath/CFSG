module

public section

namespace CFSG.Monster.B.Bin

set_option compiler.extract_closed false

abbrev Row := Array Nat

abbrev Mat := Array Row

@[expose] def nch (n : Nat) : Nat := (n + 55) / 56

@[expose] def zeros (m : Nat) : Row := Array.replicate m 0

@[expose] def xorGo (s : Row) (m : Nat) (w : Nat) (a : Row) : Row :=
  if w < m then xorGo s m (w + 1) (a.set! w (a.getD w 0 ^^^ s.getD w 0)) else a
termination_by m - w

@[inline, expose] def xorRow (m : Nat) (a s : Row) : Row := xorGo s m 0 a

@[expose] def dbl (m : Nat) (y : Row) (t : Array Row) : Array Row := t ++ t.map (xorRow m · y)

@[expose] def blockTable (m : Nat) (Y : Mat) (k : Nat) : Array Row :=
  (List.range 8).foldl (fun t i => dbl m (Y.getD (8 * k + i) (zeros m)) t) #[zeros m]

@[expose] def tableRange (m : Nat) (Y : Mat) (lo hi : Nat) : Array (Array Row) :=
  (Array.range (hi - lo)).map fun k => blockTable m Y (lo + k)

@[noinline, expose] def tableTasks (m nb : Nat) (Y : Mat) (sz : Nat) : Array (Task (Array (Array Row))) :=
  #[Task.spawn fun _ => tableRange m Y 0 (min sz nb),
    Task.spawn fun _ => tableRange m Y (min sz nb) (min (2 * sz) nb),
    Task.spawn fun _ => tableRange m Y (min (2 * sz) nb) (min (3 * sz) nb),
    Task.spawn fun _ => tableRange m Y (min (3 * sz) nb) nb]

@[noinline, expose] def tables (m nb : Nat) (Y : Mat) : Array (Array Row) :=
  (tableTasks m nb Y ((nb + 3) / 4)).foldl (fun acc t => acc ++ t.get) #[]

@[inline, expose] def byteOf (x : Row) (k : Nat) : Nat := ((x.getD (k / 7) 0) >>> (8 * (k % 7))) % 256

@[expose] def applyGo (T : Array (Array Row)) (m nb : Nat) (x : Row) (k : Nat) (acc : Row) : Row :=
  if k < nb then
    applyGo T m nb x (k + 1)
      (if byteOf x k = 0 then acc else xorRow m acc ((T.getD k #[]).getD (byteOf x k) #[]))
  else acc
termination_by nb - k

@[expose] def applyRow (T : Array (Array Row)) (m nb : Nat) (x : Row) : Row :=
  applyGo T m nb x 0 (zeros m)

@[expose] def mapRange (f : Row → Row) (X : Mat) (lo hi : Nat) : Mat := (X.extract lo hi).map f

@[noinline, expose] def parTasks (f : Row → Row) (X : Mat) (sz : Nat) : Array (Task Mat) :=
  #[Task.spawn fun _ => mapRange f X 0 sz, Task.spawn fun _ => mapRange f X sz (2 * sz),
    Task.spawn fun _ => mapRange f X (2 * sz) (3 * sz),
    Task.spawn fun _ => mapRange f X (3 * sz) (4 * sz)]

@[noinline, expose] def parMap (f : Row → Row) (X : Mat) : Mat :=
  (parTasks f X ((X.size + 3) / 4)).foldl (fun acc t => acc ++ t.get) #[]

@[noinline, expose] def mulP (n : Nat) (X Y : Mat) : Mat :=
  let m := nch n
  let nb := (n + 7) / 8
  let T := tables m nb Y
  parMap (applyRow T m nb) X

@[inline, expose] def bitOf (r : Row) (j : Nat) : Bool := (r.getD (j / 56) 0).testBit (j % 56)

@[expose] def vecGo (n m : Nat) (v : Row) (Y : Mat) (i : Nat) (acc : Row) : Row :=
  if i < n then
    vecGo n m v Y (i + 1) (if bitOf v i then xorRow m acc (Y.getD i #[]) else acc)
  else acc
termination_by n - i

@[expose] def vecMulC (n : Nat) (v : Row) (Y : Mat) : Row := vecGo n (nch n) v Y 0 (zeros (nch n))

@[expose] def unitRow (n i : Nat) : Row := (zeros (nch n)).set! (i / 56) (2 ^ (i % 56))

@[expose] def idMat (n : Nat) : Mat := Array.ofFn (n := n) fun i => unitRow n i.val

@[expose] def powM (n : Nat) (X : Mat) (e : Nat) : Mat :=
  if e = 0 then idMat n
  else if e = 1 then X
  else
    let Y := powM n (mulP n X X) (e / 2)
    if e % 2 = 1 then mulP n X Y else Y
termination_by e
decreasing_by omega

@[expose] def addM (n : Nat) (X Y : Mat) : Mat :=
  Array.ofFn (n := X.size) fun i => xorRow (nch n) X[i] (Y.getD i.val #[])


@[expose] def chunksOfNat (m x : Nat) : Row := Array.ofFn (n := m) fun w => (x >>> (56 * w.val)) % 2 ^ 56

@[expose] def matOfRows (n : Nat) (X : Array Nat) : Mat := X.map (chunksOfNat (nch n))

@[expose] def rowNe (n : Nat) (r s : Row) : Bool := (List.range n).any fun j => bitOf r j != bitOf s j

@[expose] def neM (n : Nat) (X Y : Mat) : Bool :=
  (List.range n).any fun i => rowNe n (X.getD i #[]) (Y.getD i #[])

@[expose] def findPiv (L : Mat) (c n i : Nat) : Nat :=
  if i < n then (if bitOf (L.getD i #[]) c then i else findPiv L c n (i + 1)) else n
termination_by n - i

@[expose] def swapAt (X : Mat) (i j : Nat) : Mat :=
  if i = j then X else
    let a := X.getD i #[]
    let b := X.getD j #[]
    (X.set! i b).set! j a

@[expose] def clearCol (m n r c : Nat) (pl pr : Row) (i : Nat) (L R : Mat) : Mat × Mat :=
  if i < n then
    if i ≠ r ∧ bitOf (L.getD i #[]) c then
      clearCol m n r c pl pr (i + 1) (L.modify i (xorGo pl m (c / 56) ·))
        (R.modify i (xorRow m · pr))
    else clearCol m n r c pl pr (i + 1) L R
  else (L, R)
termination_by n - i

@[expose] def gjGo (m n : Nat) (c r : Nat) (L R : Mat) (piv : Array Nat) : Mat × Mat × Array Nat :=
  if c < n then
    let p := findPiv L c n r
    if p < n then
      let L := swapAt L r p
      let R := swapAt R r p
      let pl := L.getD r #[]
      let pr := R.getD r #[]
      let LR := clearCol m n r c pl pr 0 L R
      gjGo m n (c + 1) (r + 1) LR.1 LR.2 (piv.push c)
    else gjGo m n (c + 1) r L R piv
  else (L, R, piv)
termination_by n - c

@[noinline, expose] def invM (n : Nat) (X : Mat) : Mat := (gjGo (nch n) n 0 0 X (idMat n) #[]).2.1

@[expose] def diagM (n r : Nat) : Mat :=
  Array.ofFn (n := n) fun i => if i.val < r then unitRow n i.val else zeros (nch n)

@[expose] def setBit (x : Row) (j : Nat) : Row := x.modify (j / 56) (· ||| 2 ^ (j % 56))

@[noinline, expose] def rankCert (n : Nat) (M : Mat) : Nat × Mat × Mat :=
  let res := gjGo (nch n) n 0 0 M (idMat n) #[]
  let E := res.1
  let P := res.2.1
  let piv := res.2.2
  let r := piv.size
  let isPiv : Array Bool := piv.foldl (fun a c => a.set! c true) (Array.replicate n false)
  let pos : Array Nat := (List.range n).foldl (fun (st : Array Nat × Nat) j =>
      if isPiv[j]! then (st.1.push 0, st.2) else (st.1.push (r + st.2), st.2 + 1))
    (#[], 0) |>.1
  let Q0 : Mat := Array.ofFn (n := n) fun j => if isPiv[j.val]! then zeros (nch n) else
    unitRow n pos[j.val]!
  let Q := (List.range r).foldl (fun (Q : Mat) i =>
      let row := (List.range n).foldl (fun (x : Row) j =>
          if !isPiv[j]! && bitOf E[i]! j then setBit x pos[j]! else x) (unitRow n i)
      Q.set! piv[i]! row) Q0
  (r, P, Q)

@[expose] def chunkOfBytes (n : Nat) (b : ByteArray) (o : Nat) (w : Nat) : Nat :=
  let v := (List.range 7).foldl (fun acc t =>
    acc ||| ((if 7 * w + t < 552 then (b.get! (o + 7 * w + t)).toNat else 0) <<< (8 * t))) 0
  v % 2 ^ (min 56 (n - 56 * w))

@[expose] def rowOfBytes (n : Nat) (b : ByteArray) (o : Nat) : Row :=
  Array.ofFn (n := nch n) fun w => chunkOfBytes n b o w.val

@[expose] def matOfPayload (n : Nat) (P : ByteArray) (idx : Nat) : Mat :=
  Array.ofFn (n := n) fun k => rowOfBytes n P (16 + 552 * (n * idx + k.val))

@[expose] def byteOfRow (x : Row) (b : Nat) : UInt8 := UInt8.ofNat (byteOf x b)

@[expose] def u32le (x : Nat) : Array UInt8 :=
  #[UInt8.ofNat x, UInt8.ofNat (x >>> 8), UInt8.ofNat (x >>> 16), UInt8.ofNat (x >>> 24)]

@[expose] def header (n count : Nat) : Array UInt8 := u32le 1 ++ u32le n ++ u32le count ++ u32le 69

@[expose] def payload (n : Nat) (Ms : Array Mat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := 16 + Ms.size * n * 552) fun pos =>
    if pos.val < 16 then (header n Ms.size).getD pos.val 0
    else byteOfRow ((Ms.getD ((pos.val - 16) / 552 / n) #[]).getD ((pos.val - 16) / 552 % n) #[])
      ((pos.val - 16) % 552))

@[expose] def b64Val (c : UInt8) : Nat :=
  if 65 ≤ c.toNat ∧ c.toNat ≤ 90 then c.toNat - 65
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 122 then c.toNat - 71
  else if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then c.toNat + 4
  else if c.toNat = 43 then 62 else if c.toNat = 47 then 63 else 0

@[expose] def b64Quad (b : ByteArray) (len i : Nat) (out : ByteArray) : ByteArray :=
  let v := (b64Val (b.get! i) <<< 18) ||| (b64Val (b.get! (i + 1)) <<< 12) |||
    (b64Val (b.get! (i + 2)) <<< 6) ||| b64Val (b.get! (i + 3))
  let o1 := if out.size < len then out.push (UInt8.ofNat (v >>> 16)) else out
  let o2 := if o1.size < len then o1.push (UInt8.ofNat (v >>> 8)) else o1
  if o2.size < len then o2.push (UInt8.ofNat v) else o2

@[expose] def b64Go (b : ByteArray) (len : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | fuel + 1, i, out => if out.size < len then b64Go b len fuel (i + 4) (b64Quad b len i out) else out

@[expose] def b64Decode (s : String) (len : Nat) : ByteArray :=
  b64Go s.toUTF8 len (len / 3 + 1) 0 (ByteArray.emptyWithCapacity len)

end CFSG.Monster.B.Bin

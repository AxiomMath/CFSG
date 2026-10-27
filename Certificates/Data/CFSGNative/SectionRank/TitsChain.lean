module

public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.SectionRank.Native.Tits

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

set_option compiler.extract_closed false

@[expose] def xorSel (f : Nat → Nat) (m : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => if m.testBit k then xorSel f m k ^^^ f k else xorSel f m k

@[expose] def mv (cols : List Nat) (m : Nat) : Nat :=
  xorSel (fun c => cols.getD c 0) m 52

@[expose] def genCols (_ : Unit := ()) : Array (List Nat) := #[
    [
      1, 18, 132, 8, 16,
      544, 16448, 128, 273, 512,
      1024, 34964375552, 271585280, 8192, 16384,
      32904, 66560, 34426978304, 262144, 67633152,
      269484032, 270532608, 4194304, 8396800, 17039360,
      1116725051392, 67108864, 137573433344, 268435456, 34896609280,
      1077936128, 2151677952, 4294967296, 2345203400704, 17179869184,
      34359738368, 71944896512, 137438953472, 35463544963072, 549755813888,
      1099511627776, 2336462209024, 4398046511104, 149533581377536, 299067162755072,
      35184372088832, 70368744177664, 140737488355328, 281474976710656, 562949953421312,
      1196268651020288, 2814749767106560],
    [
      4129, 66, 4, 72, 34603536,
      6176, 4160, 536887424, 256, 34734592,
      7266, 2048, 4096, 12356, 538984448,
      32768, 65792, 33685504, 4459590, 524288,
      1048576, 538968064, 4206596, 8421376, 1090584832,
      33554432, 290288316710912, 134217728, 17626814218240, 536870912,
      1073741824, 2155905024, 5385486592, 8589934592, 290838005415936,
      18726057410560, 68719476736, 139586469888, 283467841536, 9345848836096,
      18691697672192, 2267742732288, 2256481328037888, 8796093022208, 17592186044416,
      37452114821120, 2326575194308608, 140737488355328, 281474976710656, 598203044986880,
      1125899906842624, 2251799813685248],
    [
      1, 3, 12, 8, 256,
      512, 16384, 32768, 16, 32,
      65536, 67108864, 268435456, 8388608, 64,
      128, 1024, 524288, 8589934592, 131072,
      2097152, 1048576, 68719476736, 8192, 134217728,
      17179869184, 2048, 16777216, 4096, 34359738368,
      2147483648, 1073741824, 274877906944, 262144, 33554432,
      536870912, 4194304, 2199023255552, 4294967296, 549755813888,
      1099511627776, 137438953472, 4398046511104, 140737488355328, 281474976710656,
      35184372088832, 1125899906842624, 8796093022208, 17592186044416, 2251799813685248,
      70368744177664, 562949953421312],
    [
      5, 2, 4, 8, 33554432,
      1024, 8192, 536870912, 4294967296, 131072,
      32, 262144, 4194304, 64, 2097152,
      137438953472, 16777216, 512, 2048, 524288,
      1048576, 16384, 4096, 2147483648, 65536,
      16, 8796093022208, 134217728, 17592186044416, 128,
      1073741824, 8388608, 256, 70368744177664, 549755813888,
      1099511627776, 562949953421312, 32768, 4398046511104, 17179869184,
      34359738368, 35184372088832, 274877906944, 67108864, 268435456,
      2199023255552, 8589934592, 140737488355328, 281474976710656, 68719476736,
      1125899906842624, 2251799813685248]]

@[expose] def nPts (_ : Unit := ()) : Nat := 1755

@[expose] def orbitBFS (gs : Array (List Nat)) (root cap : Nat) : Array Nat := Id.run do
  let mut pts : Array Nat := #[root]
  for h in [0:cap] do
    if h < pts.size then
      let v := pts[h]!
      for g in gs do
        let w := mv g v
        if !pts.contains w then
          pts := pts.push w
  return pts

@[expose] def orbitPts (_ : Unit := ()) : Array Nat := (orbitBFS genCols (2 ^ 11) 4000).qsort (· < ·)

@[expose] def bsearch (pts : Array Nat) (v : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := pts.size
  for _ in [0:64] do
    if lo < hi then
      let mid := (lo + hi) / 2
      if pts[mid]! < v then lo := mid + 1 else hi := mid
  return if lo < pts.size && pts[lo]! == v then lo else pts.size

@[expose] def tableOf (pts : Array Nat) (cols : List Nat) : Table :=
  pts.map fun v => UInt32.ofNat (bsearch pts (mv cols v))

@[expose] def genTables (_ : Unit := ()) : Array Table := genCols.map (tableOf orbitPts)

@[expose] def orbitOK (n : Nat) (pts : Array Nat) (gs : Array (List Nat)) (tbls : Array Table) :
    Bool :=
  pts.size == n && tbls.size == gs.size && allIn 0 n (fun i => decide (pts[i]! < 2 ^ 52)) &&
    allIn 0 (n - 1) (fun i => decide (pts[i]! < pts[i + 1]!)) &&
    allIn 0 gs.size fun s => allIn 0 n fun i =>
      decide (ap tbls[s]! i < n) && pts[ap tbls[s]! i]! == mv gs[s]! pts[i]!

@[expose] def letterT (n : Nat) (tbls : Array Table) (l : Int) : Table :=
  if 0 < l ∧ l ≤ tbls.size then tbls[l.toNat - 1]!
  else if l < 0 ∧ -l ≤ tbls.size then invT n tbls[(-l).toNat - 1]!
  else idT n

@[expose] def chainWords (_ : Unit := ()) : Array (List Int) := #[
    [1],
    [2],
    [3],
    [4],
    [-1, 3, 1],
    [-4, 1, 4],
    [-3, -2, -2, 4, 2, 3],
    [-4, -3, 2, 3, 4],
    [-1, -2, -1, 2, 1, 2, 1],
    [-3, -4, -1, 3, 1, 4, 3],
    [-3, -4, -3, 4, 3, 4, 3],
    [-3, -2, -4, 2, 2, 3, -1, -2, -1, -2, 1, 2, 1, -3, -2, -2, 4, 2, 3, -4, 1, 4, -1, 3, 1],
    [-1, -3, 1, -4, -1, 4, -3, -2, -4, 2, 2, 3, -1, -2, -1, 2, 1, 2, 1, -3, -2, -2, 4, 2, -4, -3,
      4, 3, 4, -2, -4, 2, 2, 3, -1, -2, -1, -2, 1, 2, 1, -3, -2, -2, 4, 2, 3, -4, 1, 4, -1, 3, 1],
    [-3, -4, -3, -4, 3, 4, -2, -4, 2, 2, 3, -1, -2, -1, -2, 1, 2, 1, -3, -2, -2, 4, 2, 3, -4, 1,
      4, -1, 3, 1, -3, -4, -3, 4, 3, 4, 3]]

@[expose] def chainLetters (_ : Unit := ()) : Array Table :=
  buildLetters nPts (letterT nPts genTables) chainWords

@[expose] def baseVecs (_ : Unit := ()) : Array Nat := #[2048, 262144, 8589934592, 67108864]

@[expose] def chainBase (_ : Unit := ()) : Array Nat := baseVecs.map (bsearch orbitPts)

@[expose] def basisIdx (pts : Array Nat) : Array Nat := Id.run do
  let mut piv : Array Nat := Array.replicate 52 0
  let mut idx : Array Nat := #[]
  for i in [0:pts.size] do
    let mut v := pts[i]!
    for k in [0:52] do
      let b := 51 - k
      if v.testBit b && piv[b]! != 0 then v := v ^^^ piv[b]!
    if v != 0 then
      piv := piv.set! v.log2 v
      idx := idx.push i
  return idx

@[expose] def checkPts (_ : Unit := ()) : Array Nat := chainBase ++ basisIdx orbitPts

@[expose] def checkBase (_ : Unit := ()) : Array Nat := Array.range chainBase.size

@[expose] def checkVecs (_ : Unit := ()) : Array Nat := checkPts.map fun i => orbitPts[i]!

@[expose] def spanMasks (vs : Array Nat) : Array Nat := Id.run do
  let mut pv : Array Nat := Array.replicate 52 0
  let mut pm : Array Nat := Array.replicate 52 0
  for t in [0:vs.size] do
    let mut v := vs[t]!
    let mut m := 2 ^ t
    for k in [0:52] do
      let b := 51 - k
      if v.testBit b && pv[b]! != 0 then
        v := v ^^^ pv[b]!
        m := m ^^^ pm[b]!
    if v != 0 then
      pv := pv.set! v.log2 v
      pm := pm.set! v.log2 m
  for b in [0:52] do
    let mut v := pv[b]!
    let mut m := pm[b]!
    for b' in [0:b] do
      if v.testBit b' then
        v := v ^^^ pv[b']!
        m := m ^^^ pm[b']!
    pv := pv.set! b v
    pm := pm.set! b m
  return pm

@[expose] def spanOK (vs masks : Array Nat) : Bool :=
  allIn 0 52 fun c => xorSel (fun t => vs[t]!) masks[c]! vs.size == 2 ^ c

@[expose] def chainTreesT (_ : Unit := ()) : Array Tree := chainTrees nPts chainLetters chainBase

@[expose] def titsChainCheck (_ : Unit := ()) : Bool :=
  orbitOK nPts orbitPts genCols genTables && genCols.size == 4 &&
    allIn 0 4 (fun s => invOK nPts genTables[s]! (invT nPts genTables[s]!)) &&
    chainBase.size == 4 &&
    chainOK nPts chainLetters chainBase checkPts checkBase chainTreesT 3 &&
    orbitSizes chainTreesT == [1755, 1024, 5, 4] &&
    spanOK checkVecs (spanMasks checkVecs) &&
    allIn 0 4 (fun s => chainWords[s]! == [(s : Int) + 1])

end CFSG.SectionRank.Native.Tits

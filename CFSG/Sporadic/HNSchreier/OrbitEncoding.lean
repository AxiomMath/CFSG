module

public meta import Lean.Elab.Term
public meta import Certificates.Data.CFSGNative.HN.F5Orbit

public meta section
open Lean Meta Elab Term

namespace CFSG.Sporadic.HNSchreier.OrbitEncoding

def orbitBFS (d : Nat) (TA TB : Array CFSG.Sporadic.F5.Native.W17)
    (v₀ : ByteArray) (cap : Nat) : CFSG.Sporadic.F5.Native.VOrbit := Id.run do
  let mut keys := (Array.emptyWithCapacity cap).push v₀
  let mut index := (Std.HashMap.emptyWithCapacity cap).insert v₀ 0
  let mut alpha : Array UInt32 := Array.emptyWithCapacity cap
  let mut beta : Array UInt32 := Array.emptyWithCapacity cap
  let mut par : Array UInt32 := (Array.emptyWithCapacity cap).push 0
  let mut lab : Array UInt32 := (Array.emptyWithCapacity cap).push 0
  let mut h := 0
  while h < cap && h < keys.size do
    let batch := keys.extract h (min cap (min keys.size (h + 8192)))
    let tasks := (List.range ((batch.size + 1023) / 1024)).map fun chunk =>
      Task.spawn fun _ => Id.run do
        let lo := 1024 * chunk
        let hi := min (lo + 1024) batch.size
        let mut images := Array.emptyWithCapacity (hi - lo)
        for i in [lo:hi] do
          let X := batch[i]!
          images := images.push
            (CFSG.Sporadic.F5.Native.mulW d d TA X, CFSG.Sporadic.F5.Native.mulW d d TB X)
        return images
    for task in tasks do
      for (Ya, Yb) in task.get do
        match index[Ya]? with
        | some k => alpha := alpha.push (UInt32.ofNat k)
        | none =>
          index := index.insert Ya keys.size
          alpha := alpha.push (UInt32.ofNat keys.size)
          keys := keys.push Ya
          par := par.push (UInt32.ofNat h)
          lab := lab.push 1
        match index[Yb]? with
        | some k => beta := beta.push (UInt32.ofNat k)
        | none =>
          index := index.insert Yb keys.size
          beta := beta.push (UInt32.ofNat keys.size)
          keys := keys.push Yb
          par := par.push (UInt32.ofNat h)
          lab := lab.push 2
        h := h + 1
  return ⟨keys, alpha, beta, par, lab, index⟩

def vectorCodes (dimension : Nat) (vectors : Array ByteArray) : Except String (Array Nat) := do
  let mut result := Array.emptyWithCapacity vectors.size
  for v in vectors do
    unless v.size == dimension do throw "cannot encode wrong-sized F5 vector"
    let mut code := 0
    let mut offset := 0
    while offset < v.size do
      let stop := min (offset+21) v.size
      let mut word : UInt64 := 0
      for i in [offset:stop] do
        let digit := v[i]!
        unless digit.toNat < 5 do throw "cannot encode noncanonical F5 vector"
        word := word ||| (digit.toUInt64 <<< UInt64.ofNat (3*(i-offset)))
      code := code + (word.toNat <<< (3*offset))
      offset := stop
    result := result.push code
  return result

private partial def packOrbitNats (leaf branch : Name) (leafSize width : Nat)
    (xs : Array Nat) (lo hi : Nat) : Expr :=
  if hi - lo ≤ leafSize then Id.run do
    let mut bits := 0
    for i in [lo:hi] do bits := bits + (xs[i]! <<< (width * (i-lo)))
    return mkApp3 (Lean.mkConst leaf) (mkNatLit width) (mkNatLit (hi-lo)) (mkNatLit bits)
  else
    let mid := (lo+hi)/2
    mkApp3 (Lean.mkConst branch) (mkNatLit (mid-lo))
      (packOrbitNats leaf branch leafSize width xs lo mid) (packOrbitNats leaf branch leafSize width xs mid hi)

partial def emitOrbitNats (tree leaf branch : Name) (leafSize width : Nat)
    (xs : Array Nat) (lo hi : Nat) : TermElabM Expr := do
  if hi-lo ≤ 4096 then
    let name ← mkAuxDeclName `_orbitBlock
    let unit := Lean.mkConst ``Unit
    let value := mkLambda `u BinderInfo.default unit (packOrbitNats leaf branch leafSize width xs lo hi)
    let type ← mkArrow unit (Lean.mkConst tree)
    let decl := Declaration.defnDecl {
      name, levelParams := [], type, value,
      hints := .regular 0, safety := .safe }
    withOptions (Elab.async.set · false) do
      addDecl decl (forceExpose := true)
      compileDecl decl
    return mkApp (Lean.mkConst name) (Lean.mkConst ``Unit.unit)
  else
    let mid := (lo+hi)/2
    let a ← emitOrbitNats tree leaf branch leafSize width xs lo mid
    let b ← emitOrbitNats tree leaf branch leafSize width xs mid hi
    return mkApp3 (Lean.mkConst branch) (mkNatLit (mid-lo)) a b

end CFSG.Sporadic.HNSchreier.OrbitEncoding

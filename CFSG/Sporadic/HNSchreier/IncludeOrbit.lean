module

public import CFSG.Sporadic.HNSchreier.PackedOrbitData
public meta import CFSG.Sporadic.HNSchreier.OrbitEncoding
public meta import CFSG.Sporadic.HNSchreier.OrbitBuildInputs
public import CFSG.Sporadic.HNSchreier.OrbitEncoding
public import Lean.Exception

public meta section
open Lean Meta Elab Term CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native

private def orbitProgress (message : String) : TermElabM Unit := do
  logInfo message
  if let some path ← IO.getEnv "CFSG_ORBIT_PROGRESS" then
    IO.FS.withFile path .append fun h => do
      h.putStrLn message
      h.flush

elab "hn_orbit_data% " cap:num : term => do
  let started ← IO.monoMsNow
  let D := hnsBFSData
  let limit := cap.getNat
  orbitProgress s!"Running compiled F5 orbit BFS at build time (cap {limit})"
  let O := OrbitEncoding.orbitBFS D.d (D.tabA ()) (D.tabB ()) D.v0 limit
  orbitProgress s!"Compiled BFS produced {O.keys.size} vectors in {(← IO.monoMsNow)-started}ms"
  let keys ← match OrbitEncoding.vectorCodes D.d O.keys with
    | .ok xs => pure xs
    | .error message => throwError message
  orbitProgress s!"Packed vector codes in {(← IO.monoMsNow)-started}ms"
  let a := O.alpha.map UInt32.toNat
  let b := O.beta.map UInt32.toNat
  let p := O.par.map UInt32.toNat
  let l := O.lab.map UInt32.toNat
  for xs in [a,b,p] do
    unless xs.all (· < 2^32) do throwError "orbit table entry exceeds 32 bits"
  unless l.all (· < 4) do throwError "orbit label exceeds two bits"
  let emit := OrbitEncoding.emitOrbitNats ``OrbitNats ``OrbitNats.leaf ``OrbitNats.branch
  let ke ← emit 16 (3*D.d) keys 0 keys.size
  orbitProgress s!"Emitted vector blocks in {(← IO.monoMsNow)-started}ms"
  let ae ← emit 64 32 a 0 a.size
  orbitProgress s!"Emitted alpha blocks in {(← IO.monoMsNow)-started}ms"
  let be ← emit 64 32 b 0 b.size
  orbitProgress s!"Emitted beta blocks in {(← IO.monoMsNow)-started}ms"
  let pe ← emit 64 32 p 0 p.size
  orbitProgress s!"Emitted parent blocks in {(← IO.monoMsNow)-started}ms"
  let le ← emit 64 2 l 0 l.size
  let out := mkApp6 (Lean.mkConst ``PackedOrbitData.mk) (mkNatLit D.d) ke ae be pe le
  orbitProgress s!"Emitted packed orbit literals in {(← IO.monoMsNow)-started}ms; independent checks remain required"
  return out

end

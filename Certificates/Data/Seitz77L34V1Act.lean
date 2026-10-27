module

public import Certificates.Data.CFSGNative.PSL3Four.L34Syl
public meta import Certificates.Data.CFSGNative.PSL3Four.L34Syl

public section

namespace Certificates.Seitz77L34

open CFSG.PSL3Four.Native

@[expose] def v1Acts (EF ER : Array Tab) : Array Tab := Id.run do
  let idx := indexOf EF
  let mut seen : Std.HashMap Tab Unit := {}
  let mut out : Array Tab := #[]
  for r in ER do
    let ri := invTab 42 r
    let img := EF.map fun f => posOf idx EF (conjTab 42 r ri f)
    if allBelow EF.size
        (fun i => img[i]! < EF.size && EF[img[i]!]! == conjTab 42 r ri EF[i]!) then
      if !seen.contains img then
        seen := seen.insert img ()
        out := out.push img
  return out

@[expose] def l34V1ActCheck (ER : Array Tab) : Bool :=
  let EF := enumBFS 42 fGens 16
  let acts := v1Acts EF.tabs ER
  let idF := idTab 16
  let invs := acts.filter fun s => comp 16 s s == idF
  enumOK 42 fGens EF && EF.tabs.size == 16 &&
    (allBelow acts.size fun a =>
      acts[a]! == idF || countBelow 16 (fun i => acts[a]![i]! == i) ≤ 4) &&
    (allBelow invs.size fun a => allBelow invs.size fun b => allBelow invs.size fun c =>
      invs[a]! == idF || invs[b]! == idF || invs[b]! == invs[a]! ||
        !(comp 16 invs[a]! invs[b]! == comp 16 invs[b]! invs[a]! &&
          comp 16 invs[a]! invs[c]! == comp 16 invs[c]! invs[a]! &&
          comp 16 invs[b]! invs[c]! == comp 16 invs[c]! invs[b]!) ||
        invs[c]! == idF || invs[c]! == invs[a]! || invs[c]! == invs[b]! ||
        invs[c]! == comp 16 invs[a]! invs[b]!)

end Certificates.Seitz77L34

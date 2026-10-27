module

public import CFSG.Monster.B.TwoA.Fischer.CertSeed
public import CFSG.Monster.B.TwoA.Fischer.CertRemText
public import Certificates.Data.CFSGNative.MonsterB.BinarySha
public import Std.Data.HashSet
public meta import CFSG.Monster.B.TwoA.Fischer.CertSeed
public meta import CFSG.Monster.B.TwoA.Fischer.CertRemText
public meta import Certificates.Data.CFSGNative.MonsterB.BinarySha

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer.Cert

open Lean (Json)
open CFSG.Monster.B.Fischer CFSG.Monster.B.Binary.Native CFSG.Sporadic.SmallF2
  CFSG.Sporadic.SmallF2.Native
open scoped Matrix

@[expose] def remSeed : ℕ := 16058837527637121392057

@[expose] def remTree : Array ℕ × Array ℕ × Array ℕ := Id.run do
  let mut vecs : Array ℕ := #[remSeed]
  let mut pars : Array ℕ := #[0]
  let mut gens : Array ℕ := #[0]
  let mut seen : Std.HashSet ℕ := (Std.HashSet.emptyWithCapacity 1048576).insert remSeed
  let mut h := 0
  for _ in [0:700000] do
    if h < vecs.size then
      let v := vecs[h]!
      for k in [0:4] do
        let w := vecMulN 78 (fourColArr[k]!) v
        if !seen.contains w then
          seen := seen.insert w
          vecs := vecs.push w
          pars := pars.push h
          gens := gens.push k
      h := h + 1
  return (vecs, pars, gens)

@[expose] def recordsOf (vecs pars gens : Array ℕ) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.emptyWithCapacity (15 * vecs.size)
  for i in [0:vecs.size] do
    let v := vecs[i]!
    for j in [0:10] do
      b := b.push (UInt8.ofNat ((v >>> (8 * j)) % 256))
    let p := if i == 0 then 0xffffffff else pars[i]!
    for j in [0:4] do
      b := b.push (UInt8.ofNat ((p >>> (8 * j)) % 256))
    b := b.push (UInt8.ofNat (if i == 0 then 0xff else gens[i]!))
  return b

@[expose] def remDecompressedSha : ℕ :=
  0x673d59a1b62a7c97d5142ceed45d3e2497e35d36a597af91ab15abfb0ae2b1d8

@[expose] def treeOK (vecs pars gens : Array ℕ) : Bool :=
  vecs.size == 694980 && vecs[0]! == remSeed &&
    ((List.range 694980).all fun i =>
      decide (vecs[i]! < 2 ^ 78) &&
        (i == 0 || (decide (pars[i]! < i) && decide (gens[i]! < 4) &&
          vecs[i]! == vecMulN 78 (fourColArr[gens[i]!]!) vecs[pars[i]!]!))) &&
    strictSorted (vecs.toList.mergeSort)

@[expose] def remCheck : Bool :=
  let t := remTree
  let r := recordsOf t.1 t.2.1 t.2.2
  treeOK t.1 t.2.1 t.2.2 && r.size == 10424700 && sha256Nat r == remDecompressedSha

@[expose] def remManifestSha : ℕ :=
  0x67090660b01a22a1902dab4396546c80225fb678a85e6b4bbb5d1978f624c773

@[expose] def remScriptSha : ℕ :=
  0xe69b70adf45147ddcb90359f42f39bf9aa86b64a3537e36d16654558db2e17ae

@[expose] def remManifestCheck : Bool :=
  match (do
    let j ← Json.parse remManifestText
    let t ← j.getObjVal? "orbit_tree"
    pure (← j.getObjValAs? ℕ "root_seed", ← j.getObjValAs? ℕ "orbit_size",
      ← j.getObjValAs? (List (List ℕ)) "four_native_generator_columns",
      ← t.getObjValAs? String "path", ← t.getObjValAs? String "sha256",
      ← t.getObjValAs? String "decompressed_sha256", ← t.getObjValAs? ℕ "decompressed_bytes",
      ← t.getObjValAs? ℕ "record_bytes") : Except String _) with
  | .ok (seed, size, cols, path, gz, dsha, dbytes, rbytes) =>
    seed == remSeed && size == 694980 && cols == dAlgRec.fourModuleGeneratorColumns &&
      path == "MON-Fischer-remaining-root-orbit-tree.bin.gz" &&
      gz == "4cc19e1dee6b56d5f26554cf4c157a0df81c8d031e8bbeeb822f63259d59c6ec" &&
      parseHexNat dsha == remDecompressedSha && dbytes == 10424700 && rbytes == 15
  | .error _ => false

end CFSG.Monster.B.TwoA.Fischer.Cert

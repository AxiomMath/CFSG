module

public import Certificates.Data.PermutationCatalogue

public section

namespace CFSG.Certificates.PermutationCatalogue.Json

open CFSG.PSL3Four.Native
open CFSG.Certificates.PermutationCatalogue.Data

structure Parsed (n : Nat) where
  ok : Bool
  input : Input
deriving Inhabited

@[inline] def readTab (w : Nat → Nat) (base n : Nat) : Tab :=
  Array.ofFn (n := n) fun i => w (base + i.val)

@[inline] def readArr (w : Nat → Nat) (base n : Nat) : Array Nat :=
  Array.ofFn (n := n) fun i => w (base + i.val)

@[inline] def tabBelow (n : Nat) (t : Tab) : Bool :=
  t.all fun x => x < n

@[inline] def base64Val (c : UInt8) : Nat :=
  if c ≥ 65 && c ≤ 90 then c.toNat - 65
  else if c ≥ 97 && c ≤ 122 then c.toNat - 71
  else if c ≥ 48 && c ≤ 57 then c.toNat + 4
  else if c == 43 then 62
  else if c == 47 then 63
  else 0

@[expose] def decodeBase64 (s : String) (size : Nat) : ByteArray := Id.run do
  let src := s.toUTF8
  let mut out : ByteArray := ByteArray.emptyWithCapacity size
  let mut acc := 0
  let mut bits := 0
  let mut i := 0
  let mut n := 0
  while i < src.size && n < size do
    acc := (acc <<< 6) ||| base64Val src[i]!
    bits := bits + 6
    i := i + 1
    if bits ≥ 8 then
      bits := bits - 8
      out := out.push (UInt8.ofNat ((acc >>> bits) &&& 255))
      acc := acc &&& ((1 <<< bits) - 1)
      n := n + 1
  return out

@[expose] def parse (w : Nat → Nat) (wordCount degree rows ambient ambientGens bottom : Nat) :
    Parsed degree := Id.run do
  let fail : Parsed degree := ⟨false, default⟩
  if wordCount < 9 then return fail
  let hdr := readArr w 0 9
  if hdr[0]! != 0x5033 || hdr[1]! != 1 || hdr[2]! != degree || hdr[3]! != rows ||
      hdr[4]! != ambient || hdr[5]! != ambient || hdr[6]! != bottom then
    return fail
  let total := hdr[7]! + (hdr[8]! <<< 16)
  if total != wordCount then return fail
  let mut pos := 9
  if pos + ambient * degree > wordCount then return fail
  let mut ambientTabs : Array Tab := Array.mkEmpty ambient
  for _ in [0:ambient] do
    ambientTabs := ambientTabs.push (readTab w pos degree)
    pos := pos + degree
  if !ambientTabs.all (tabBelow degree) then return fail
  if pos + ambient > wordCount then return fail
  let ambientPar := readArr w pos ambient
  pos := pos + ambient
  for i in [0:ambient] do
    if i != 0 && ambientPar[i]! >= i then return fail
  if pos + ambient > wordCount then return fail
  let ambientLab := readArr w pos ambient
  pos := pos + ambient
  if ambientGens != 0 then
    for i in [0:ambient] do
      if i != 0 && ambientLab[i]! >= ambientGens then return fail
  if pos + ambient * degree > wordCount then return fail
  let mut ambientInv : Array Tab := Array.mkEmpty ambient
  for _ in [0:ambient] do
    ambientInv := ambientInv.push (readTab w pos degree)
    pos := pos + degree
  if !ambientInv.all (tabBelow degree) then return fail
  let mut rowList : Array Row := Array.mkEmpty rows
  for _ in [0:rows] do
    if pos + 1 > wordCount then return fail
    let gensN := w pos
    pos := pos + 1
    if pos + gensN > wordCount then return fail
    let gens := readArr w pos gensN
    pos := pos + gensN
    if !(gens.all fun g => g < ambient) then return fail
    if pos + 1 > wordCount then return fail
    let elemsN := w pos
    pos := pos + 1
    if pos + elemsN * degree > wordCount then return fail
    let mut elemsTabs : Array Tab := Array.mkEmpty elemsN
    for _ in [0:elemsN] do
      elemsTabs := elemsTabs.push (readTab w pos degree)
      pos := pos + degree
    if !elemsTabs.all (tabBelow degree) then return fail
    if pos + 2 * elemsN > wordCount then return fail
    let elemsPar := readArr w pos elemsN
    pos := pos + elemsN
    let elemsLab := readArr w pos elemsN
    pos := pos + elemsN
    for i in [0:elemsN] do
      if i != 0 && elemsPar[i]! >= i then return fail
    if gensN != 0 then
      for i in [0:elemsN] do
        if i != 0 && elemsLab[i]! >= gensN then return fail
    if pos + 1 > wordCount then return fail
    let transN := w pos
    pos := pos + 1
    let mut transList : Array Transition := Array.mkEmpty transN
    for _ in [0:transN] do
      if pos + 4 > wordCount then return fail
      let rep := w pos
      let conj := w (pos + 1)
      let target := w (pos + 2)
      let nwords := w (pos + 3)
      pos := pos + 4
      if rep >= ambient || conj >= ambient || target >= rows then return fail
      let mut words : Array (Array (Option Nat)) := Array.mkEmpty nwords
      for _ in [0:nwords] do
        if pos + 1 > wordCount then return fail
        let n := w pos
        pos := pos + 1
        if pos + n > wordCount then return fail
        let mut word : Array (Option Nat) := Array.mkEmpty n
        for _ in [0:n] do
          let x := w pos
          pos := pos + 1
          if x == 0 then
            word := word.push none
          else
            if x - 1 >= gensN then return fail
            word := word.push (some (x - 1))
        words := words.push word
      transList := transList.push
        { representative := rep, conjugator := conj, target := target, words := words }
    if pos + 1 > wordCount then return fail
    let coverN := w pos
    pos := pos + 1
    if coverN != ambient then return fail
    let mut coverList : Array Cover := Array.mkEmpty coverN
    for _ in [0:coverN] do
      if pos + 3 > wordCount then return fail
      let u := w pos
      let left := w (pos + 1)
      let right := w (pos + 2)
      pos := pos + 3
      if u >= transN || left >= elemsN || right >= elemsN then return fail
      coverList := coverList.push { transition := u, left := left, right := right }
    rowList := rowList.push
      { gens := gens
        elems := { tabs := elemsTabs, par := elemsPar, lab := elemsLab }
        transitions := transList
        cover := coverList }
  if pos != wordCount then return fail
  for r in rowList do
    for t in r.transitions do
      if t.target >= rowList.size then return fail
      if t.words.size != rowList[t.target]!.gens.size then return fail
  return { ok := true
           input := { ambient := { tabs := ambientTabs, par := ambientPar, lab := ambientLab }
                      ambientInv := ambientInv
                      rows := rowList
                      bottom := bottom } }

end CFSG.Certificates.PermutationCatalogue.Json

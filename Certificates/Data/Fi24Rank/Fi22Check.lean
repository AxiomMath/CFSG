module

public import Certificates.Data.Fi24Rank.Common
public import Certificates.Data.Fi24Rank.Fi22Data
public import Certificates.Data.CFSGNative.Fi22.Nfp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.F3.Native

set_option compiler.extract_closed false

@[expose] def fi22RA (_ : Unit := ()) : Array (Array Nat) := rowsOf 3510 (hexNums 3 fi22RAText)

@[expose] def fi22RG (_ : Unit := ()) : Array (Array Nat) := rowsOf 3510 (hexNums 3 fi22RGText)

@[expose] def fi22RMu (_ : Unit := ()) : Array (Array Nat) := rowsOf 243 (hexNums 2 fi22RMuText)

@[expose] def fi22RChain (_ : Unit := ()) : Array Nat := hexNums 3 fi22RChainText

@[expose] def fi22RPos (_ : Unit := ()) : Array Nat := Id.run do
  let ch := fi22RChain ()
  let mut pos : Array Nat := Array.replicate 3510 0
  for c in [0:ch.size / 3] do
    pos := pos.set! ch[3 * c]! (c + 1)
  return pos

@[expose] def fi22TauOK (_ : Unit := ()) : Bool :=
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  let S := fi22RA () ++ fi22RG ()
  allLt 7 fun k =>
    let s := S[k]!
    let r := invCand 3510 s
    allLt 6 fun j =>
      let b := CFSG.Sporadic.Fi22.Native.nfpBase[j]!
      let Tb := CFSG.Sporadic.Fi22.Native.tabOf O b
      let Ts := CFSG.Sporadic.Fi22.Native.tabOf O s[b]!
      decide (s[b]! < 3510) && allLt 3510 fun x => s[ap Tb r[x]!]! == ap Ts x

@[expose] def fi22PosOK (_ : Unit := ()) : Bool :=
  let O := CFSG.Sporadic.Fi22.Native.orbitData ()
  let ch := fi22RChain ()
  let pos := fi22RPos ()
  let I := iotas 3510 (fi22RA ())
  let S := stabs 3510 I
  pos.size == 3510 &&
  parLt 3510 8 fun q =>
    if pos[q]! == 0 then uniqAt 3510 I S q
    else
      let c := pos[q]! - 1
      let x := ch[3 * c + 1]!
      let y := ch[3 * c + 2]!
      decide (3 * c + 2 < ch.size) && ch[3 * c]! == q && decide (x < 3510) && decide (y < 3510) &&
        decide (pos[x]! ≤ c) && decide (pos[y]! ≤ c) &&
        ap (CFSG.Sporadic.Fi22.Native.tabOf O x) y == q

@[expose] def fi22RankOK (_ : Unit := ()) : Bool :=
  sideOK 3510 (fi22RA ()) (fi22RG ()) (fi22RMu ()) fi22RP0 81 && nonabOK (fi22RMu ()) 81 &&
    fi22TauOK () && fi22PosOK ()

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative

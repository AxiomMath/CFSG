module

public import Init.Data.String.Defs

public section

namespace CFSG.Sporadic.HNSchreier.Native

@[inline, expose] def isHexDigitB (c : UInt8) : Bool :=
  (48 ≤ c.toNat && c.toNat < 58) || (97 ≤ c.toNat && c.toNat < 103)

@[inline, expose] def hexValB (c : UInt8) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else c.toNat - 87

@[expose] def hexDumpBytes (s : String) : ByteArray := Id.run do
  let b := s.toUTF8
  let mut out : ByteArray := ByteArray.emptyWithCapacity (b.size / 2)
  let mut body := false
  let mut hi := 0
  let mut half := false
  for c in b do
    if !body then
      if c == 10 then body := true
    else if isHexDigitB c then
      if half then
        out := out.push (UInt8.ofNat (16 * hi + hexValB c))
        half := false
      else
        hi := hexValB c
        half := true
  return out


end CFSG.Sporadic.HNSchreier.Native

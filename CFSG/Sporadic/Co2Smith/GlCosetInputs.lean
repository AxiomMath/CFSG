module

public import CFSG.Sporadic.Co2Smith.GlDataInputs
public import CFSG.Sporadic.Co2Smith.GlCosetWords

public section

namespace CFSG.Sporadic.Co2Smith.Native

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Co2Cert

set_option compiler.extract_closed false

@[expose] def glCzWords : List (List Nat) := glCzLetters.map (fun k => [k]) ++ [glUWord]

@[expose] def glCosetElemOK : Bool :=
  glMaps glZ 80 80 && glMaps glRows[14]! 80 80 && glMaps glRows[14]! 1172 1339 &&
    glMaps glW0 80 80 && glMaps glB3 80 80 && glMaps glB3 942 1172 && glMaps glB3 582 1348 &&
    glMaps glU 1348 728 && glMaps glW0 728 1172 &&
    glMaps (mulRows 22 glV1 glZ) 582 1977 && (glWit0Pts 1).contains 1977 &&
    glM2Words.all (fun w => glMaps (glR w) 80 80 && glMaps (glR w) 582 582) &&
    glMaps (glR glM2Words[0]!) 942 942

@[expose] def glChainM2OK : Bool := glChainOK glM2Words glChainM2Base glChainM2W 13063680

@[expose] def glChainCzOK : Bool :=
  glCzLetters.all (fun k => glMaps (glR [k]) 80 80) &&
    glChainOK glCzWords glChainCzBase glChainCzW 743178240

@[expose] def glCosetLabOK : Bool :=
  CFSG.Sporadic.Co2Rank3.stabRec.1[glCArr[578]!]! == 36 &&
    CFSG.Sporadic.Co2Rank3.stabRec.1[glCArr[3]!]! == 4 &&
    CFSG.Sporadic.Co2Rank3.stabRec.1[glCArr[487]!]! == 5 &&
    CFSG.Sporadic.Co2Rank3.p01Rec.1[glCArr[3]!]! == 4 &&
    CFSG.Sporadic.Co2Rank3.p0Rec.1[2]! == 1 && CFSG.Sporadic.Co2Rank3.p0Rec.1[8]! == 1 &&
    [578, 3, 487, 1172].all (fun x => (glWit0Pts 1).contains x)

end CFSG.Sporadic.Co2Smith.Native

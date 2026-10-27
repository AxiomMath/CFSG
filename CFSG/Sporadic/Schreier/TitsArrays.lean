module

public import CFSG.Sporadic.Schreier.TitsData
public import Certificates.Data.CFSGNative.MonsterB.Co2Data

public section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Monster.B.Co2.Native (hexAt)

@[expose] def titsBytes1755 : ByteArray := titsPerm1755Text.toUTF8

@[expose] def titsBytes8775 : ByteArray := titsPerm8775Text.toUTF8

@[expose] def titsBytes2925 : ByteArray := titsPerm2925Text.toUTF8

@[expose] def titsMapsBytes : ByteArray := titsMapsText.toUTF8

@[expose] def titsMergesBytes : ByteArray := titsMergesText.toUTF8

@[expose, irreducible] def titsArr1755 (L : Nat) : Array Nat :=
  Array.ofFn (n := 1755) fun i => hexAt titsBytes1755 (3 * (1755 * L + i.val)) 3

@[expose, irreducible] def titsArr8775 (L : Nat) : Array Nat :=
  Array.ofFn (n := 8775) fun i => hexAt titsBytes8775 (4 * (8775 * L + i.val)) 4

@[expose, irreducible] def titsArr2925 (L : Nat) : Array Nat :=
  Array.ofFn (n := 2925) fun i => hexAt titsBytes2925 (3 * (2925 * L + i.val)) 3

@[expose] def titsField1755 (L₀ m : Nat) : Array (Array Nat) :=
  Array.ofFn (n := m) fun j => titsArr1755 (L₀ + j.val)

@[expose] def titsGenArrs : Array (Array Nat) := titsField1755 0 4

@[expose] def titsAmbientArrs : Array (Array Nat) := titsField1755 4 14

@[expose] def titsDerivedArrs : Array (Array Nat) := titsField1755 18 13

@[expose] def titsPerfectArrs : Array (Array Nat) := titsField1755 31 12

@[expose] def titsFlagArrs : Array (Array Nat) :=
  Array.ofFn (n := 4) fun j => titsArr8775 j.val

@[expose, irreducible] def titsBetaArr : Array Nat :=
  Array.ofFn (n := 8775) fun i => hexAt titsMapsBytes (3 * i.val) 3

@[expose, irreducible] def titsMergeAt (k : Nat) : Nat × Nat × Nat :=
  (hexAt titsMergesBytes (7 * k) 1, hexAt titsMergesBytes (7 * k + 1) 3,
    hexAt titsMergesBytes (7 * k + 4) 3)

@[expose] def titsOrigMergeVals (l : Nat) : List (Nat × Nat × Nat) :=
  (List.range 1753).map fun k => titsMergeAt (1753 * l + k)

@[expose] def titsHArrs : Array (Array Nat) := titsField1755 43 9

@[expose] def titsSArrs : Array (Array Nat) := titsField1755 52 9

@[expose] def titsNArrs : Array (Array Nat) := titsField1755 61 10

@[expose] def titsJArrs : Array (Array Nat) := titsField1755 71 9

@[expose] def titsKArrs : Array (Array Nat) := titsField1755 80 7

@[expose] def titsRArrs : Array (Array Nat) := titsField1755 87 8

@[expose] def titsAStarArrs : Array (Array Nat) :=
  Array.ofFn (n := 4) fun j => titsArr2925 j.val

@[expose] def titsDFlagStored : Array (Array Nat) :=
  Array.ofFn (n := 2) fun j => titsArr8775 (4 + j.val)

@[expose] def titsDStarStored : Array (Array Nat) :=
  Array.ofFn (n := 2) fun j => titsArr2925 (4 + j.val)

@[expose, irreducible] def titsKappaArr : Array Nat :=
  Array.ofFn (n := 8775) fun i => hexAt titsMapsBytes (3 * (8775 + i.val)) 3

@[expose] def titsOtherMergeVals (l : Nat) : List (Nat × Nat × Nat) :=
  (List.range 2923).map fun k => titsMergeAt (4 * 1753 + 2923 * l + k)

@[expose] def titsSigmaArr : Array Nat := titsArr1755 95

end CFSG.Sporadic.Schreier.Tits

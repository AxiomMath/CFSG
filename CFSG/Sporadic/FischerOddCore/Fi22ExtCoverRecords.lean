module

public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import Certificates.Data.CFSGNative.Co3Schreier.Basic

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Sporadic.FischerOddCore.Native CFSG.Sporadic.Schreier.Co3.Native

@[expose] def fi22ExtRootsRec : Array Nat := #[
  98543, 49886, 97798, 683, 10361, 76334, 50619, 6964, 230801, 106615, 96778, 261225, 211390,
  150707, 10848, 37965, 75135, 249340, 100147, 218886, 199064, 136675, 184640, 200070, 254925,
  56560, 218483, 19720, 51727, 254988, 214124, 39578, 140527, 168166, 131041, 202095, 70164, 214,
  243935, 240597, 49840, 249205, 112418, 210610, 216932, 99612, 157200, 12132, 6508, 77850, 36073,
  3314, 144820, 257460, 246950, 120836, 171067, 16416, 184332, 243709, 261716, 8200, 25808,
  163495, 163267, 102736, 246194, 112953, 32530, 50568, 25698, 68156, 256, 108518, 257554, 49728,
  144704, 201370, 788]

@[expose] def fi22ExtInvRecText : String := include_str "Fi22ExtInvRec.txt"

@[expose] def fi22ExtInvRecLines : Array (Array Nat) :=
  Array.ofFn (n := 48) fun L => hexLine fi22ExtInvRecText.toUTF8 5 1920 L.val

@[expose] def fi22ExtInvRec (k f : Nat) : Nat := fi22ExtInvRecLines[k / 128]![k % 128 * 15 + f]!

@[expose] def fi22ExtInvPos : Array Nat :=
  (List.range 6143).foldl (fun A k => A.set! (fi22ExtInvRec k 14) k) (Array.replicate 262144 6143)

@[expose] def fi22ExtInvField (f d I : Nat) : Nat :=
  if fi22ExtInvPos[I]! < 6143 then fi22ExtInvRec fi22ExtInvPos[I]! f else d

@[expose] def fi22ExtLabelsRec : LabelCert :=
  ⟨Array.ofFn (n := 262144) fun I => fi22ExtInvField 0 79 I.val,
    Array.ofFn (n := 262144) fun I => fi22ExtInvField 1 0 I.val,
    Array.ofFn (n := 262144) fun I => fi22ExtInvField 2 0 I.val,
    Array.ofFn (n := 262144) fun I => fi22ExtInvField 3 0 I.val,
    Array.ofFn (n := 2621440) fun t => fi22ExtInvField (4 + t.val % 10) 0 (t.val / 10)⟩

end CFSG.Sporadic.FischerOddCore

end

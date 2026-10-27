module

public import CFSG.Sporadic.SuzRecog.SuzL34Cert.CheckModel

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

@[expose] def l1TabsClosureCheck (_ : Unit := ()) : Bool :=
  let L := l1Tabs ()
  let B := decs l1Decs
  allBelow 4 (fun k => L[2 ^ k]! == B[k]!) &&
    allBelow L.size (fun k => permOK 1782 L[k]!) &&
    anyBelow L.size (fun k => L[k]! == idTab 1782) &&
    (allBelow L.size fun i =>
      allBelow L.size fun j =>
        anyBelow L.size fun k => L[k]! == comp 1782 L[i]! L[j]!) &&
    (allBelow L.size fun i =>
      anyBelow L.size fun k => comp 1782 L[i]! L[k]! == idTab 1782) &&
    decide L.toList.Nodup &&
    allBelow L.size (fun k => found (indexOf L) L L[k]!)

@[expose] def m21KClosureCheck (_ : Unit := ()) : Bool :=
  let M := m21Tabs ()
  let N := m21Decs
  let K := decs l1CompDecs
  N.all (fun d => permOK 1782 (decTab d)) &&
    allBelow 4 (fun k => M[2 ^ k]! == (decs N)[k]!) &&
    allBelow M.size (fun k => permOK 1782 M[k]!) &&
    anyBelow M.size (fun k => M[k]! == idTab 1782) &&
    (allBelow M.size fun i =>
      allBelow M.size fun j =>
        anyBelow M.size fun k => M[k]! == comp 1782 M[i]! M[j]!) &&
    (allBelow M.size fun i =>
      anyBelow M.size fun k => comp 1782 M[i]! M[k]! == idTab 1782) &&
    decide M.toList.Nodup &&
    allBelow M.size (fun k => found (indexOf M) M M[k]!) &&
    l1CompDecs.all (fun d => permOK 1782 (decTab d)) &&
    enumOK 1782 K (enumBFS 1782 K 4)

end CFSG.Sporadic.SuzRecog.SuzL34Cert

module

public import CFSG.Quasithin.H13.LocDblHeData
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public meta import CFSG.Quasithin.H13.LocDblHeData
public import Certificates.Data.CFSGNative.H13.LocDblDc
public meta import Certificates.Data.CFSGNative.H13.LocDblDc
public meta import CFSG.Quasithin.H13.LocDblHeEdges1
public meta import CFSG.Quasithin.H13.LocDblHeEdges2
public meta import CFSG.Quasithin.H13.LocDblHeEdges3
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public meta import Certificates.Data.CFSGNative.He.Certificate

public section

namespace CFSG.Quasithin.H13.LocDbl.HeCert

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.LocDbl.DcNative

open CFSG.Sporadic.Th.Native (ap)

@[expose] def ta : Array Nat :=
  ((List.range 8330).map (ap (CFSG.Sporadic.He.Native.orbitData ()).alpha)).toArray

@[expose] def tb : Array Nat :=
  ((List.range 8330).map (ap (CFSG.Sporadic.He.Native.orbitData ()).beta)).toArray

@[expose] def AB : Array (Array Nat) := #[ta, tb, invTab ta, invTab tb]

@[expose] def qn : List Nat := heQp.map Prod.fst

@[expose] def RT : Array (Array Nat) := (qn.map fun i => (slpTabsA ta tb heProg)[i]!).toArray

@[expose] def B : List Nat := CFSG.Sporadic.He.Native.chainBase.toList

@[expose] def enumR : Array Nat × Array Nat := bfsEnumL 8330 B RT 2000

@[expose] def vs : List (List (List Nat) × Array Nat × Array Nat × Nat) :=
  vData.map fun V =>
    let e := bfsEnumL 8330 B (RT ++ (V.1.map (tabW 8330 AB)).toArray) (V.2 + 10)
    (V.1, e.1, e.2, V.2)

@[expose] def heD : DcData where
  n := 8330
  B := B
  AB := AB
  RT := RT
  RTi := RT.map invTab
  NR := 1024
  rpar := enumR.1
  rlab := enumR.2
  lb := orbitLabels 8330 RT
  reps := parseWords repsStr
  edges := parseEdges edgesStr
  c0 := root
  inEdge := parseNats inEdgeStr
  dIn := parseNats dInStr
  reach := (parseNats reachStr).toList
  outEdge := parseNats outEdgeStr
  dOut := parseNats dOutStr
  Vs := vs
  order := 4030387200

end CFSG.Quasithin.H13.LocDbl.HeCert

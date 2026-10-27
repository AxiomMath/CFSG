module

public import CFSG.Quasithin.H13.LocDblJ2Data
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public meta import CFSG.Quasithin.H13.LocDblJ2Data
public import Certificates.Data.CFSGNative.H13.LocDblDc
public meta import Certificates.Data.CFSGNative.H13.LocDblDc
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicJ2
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicBaseNative
public meta import Certificates.Data.CFSGNative.J2.Certificate

public section

namespace CFSG.Quasithin.H13.LocDbl.J2Cert

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.H13.LocDbl.DcNative

@[expose] def ta : Array Nat := j2ta.toArray

@[expose] def tb : Array Nat := j2tb.toArray

@[expose] def AB : Array (Array Nat) := #[ta, tb, invTab ta, invTab tb]

@[expose] def qn : List Nat := j2Qp.map Prod.fst

@[expose] def RT : Array (Array Nat) := (qn.map fun i => (slpTabsA ta tb j2Prog)[i]!).toArray

@[expose] def B : List Nat := List.range 315

@[expose] def enumR : Array Nat × Array Nat := bfsEnumL 315 B RT 200

@[expose] def vs : List (List (List Nat) × Array Nat × Array Nat × Nat) :=
  vData.map fun V =>
    let e := bfsEnumL 315 B (RT ++ (V.1.map (tabW 315 AB)).toArray) (V.2 + 10)
    (V.1, e.1, e.2, V.2)

@[expose] def j2D : DcData where
  n := 315
  B := B
  AB := AB
  RT := RT
  RTi := RT.map invTab
  NR := 128
  rpar := enumR.1
  rlab := enumR.2
  lb := orbitLabels 315 RT
  reps := parseWords repsStr
  edges := parseEdges edgesStr
  c0 := root
  inEdge := parseNats inEdgeStr
  dIn := parseNats dInStr
  reach := (parseNats reachStr).toList
  outEdge := parseNats outEdgeStr
  dOut := parseNats dOutStr
  Vs := vs
  order := 604800

end CFSG.Quasithin.H13.LocDbl.J2Cert

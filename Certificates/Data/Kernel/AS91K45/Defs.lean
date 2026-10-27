module

public import Certificates.Data.Kernel.HJ12KT

public section

noncomputable section

namespace Certificates.Kernel.AS91K45

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K

@[expose] def nGensQ : List ℕ :=
  [11151733896890032821475586019756144924315655, 18143202638049872146410063341699308803141363,
    5365497657942450660064270864226479759481008, 11151733896890032821475586019756144924315655,
    14295200262100043786427221488448615565533260, 4532015868322888836756544095819466405298366]

@[expose] def nGensL : List (List ℕ) :=
  [[7, 517, 515, 398, 16, 32, 448, 840, 712, 518, 1024, 2048],
    [3827, 274, 273, 811, 1292, 304, 571, 1412, 1348, 2508, 1556, 3332],
    [2224, 77, 3619, 3763, 1567, 1423, 3090, 844, 2267, 3273, 1991, 985],
    [7, 517, 515, 398, 16, 32, 448, 840, 712, 518, 1024, 2048],
    [76, 74, 4014, 593, 1142, 104, 833, 705, 1086, 1545, 2513, 2625],
    [190, 2684, 2098, 1842, 3865, 845, 4028, 3861, 3218, 3246, 1637, 832]]

@[expose] def pQ : List ℕ :=
  [5659596365045704864721142394808995562925057, 8389322472514166039870025575933217047846913,
    9820219706086004407936704308795961903113461, 6705195021291883877282066692790280271374129]

@[expose] def gZQ : List ℕ :=
  [2573156193824583219788479952312110266815962, 15005501897667644566228494022703296583526645]

@[expose] def p2Q : List ℕ :=
  [11151733957229567414412306689924932879568910, 12197336538852166835894624241825581228053302,
    11151737882606002682240727521210012664878086, 11168067448534241732814282915841850317236229]

@[expose] def omegaQ : ℕ := 11325979737014698116079553641009599731990592

@[expose] def stab1Q : List ℕ :=
  [9434929166451097896438921821798529162777402, 12213670154771886511627129256773722586737469,
    18006079095044621266145188812148444575686174, 16574495776676400334896268313581167974699302,
    7234812525802977909957055696742283841904641]

@[expose] def stab1W : List (List ℕ) :=
  [[3, 4, 4, 5, 5, 3, 2, 2, 2, 0, 2, 0, 1, 2, 2, 0],
    [4, 3, 5, 3, 4, 4, 3, 4, 4, 0, 1, 1, 0, 1, 1, 0, 2, 0, 1],
    [3, 4, 3, 4, 5, 3, 2, 1, 0, 1, 1, 0, 1, 0, 1],
    [3, 4, 5, 5, 4, 5, 3, 5, 1, 2, 0, 1, 1, 0, 2, 0, 1],
    [4, 3, 5, 3, 4, 3, 5, 0, 2, 2, 0, 2, 1, 0, 1, 0]]

@[expose] def w1L : List ℕ :=
  [0, 3, 40, 43, 192, 195, 232, 235, 276, 279, 316, 319, 468, 471, 508, 511,
    1028, 1031, 1068, 1071, 1220, 1223, 1260, 1263, 1296, 1299, 1336, 1339, 1488, 1491, 1528, 1531,
    2560, 2563, 2600, 2603, 2752, 2755, 2792, 2795, 2836, 2839, 2876, 2879, 3028, 3031, 3068, 3071,
    3588, 3591, 3628, 3631, 3780, 3783, 3820, 3823, 3856, 3859, 3896, 3899, 4048, 4051, 4088, 4091]

@[expose] def wordP (gs : List ℕ) (w : List ℕ) : ℕ := (w.map fun i => gs.getD i oneQ).foldr mulQ oneQ

@[expose] def stab1OK : Bool := stab1W.map (wordP nGensQ) == stab1Q

@[expose] def fixAll (gs : List ℕ) : ℕ := gs.foldl (fun m g => m &&& fixMask (unpackQ g)) fullM

@[expose] def stepWK (acc : List (List ℕ) × NT ℕ) (t : List ℕ) (k : ℕ) : List (List ℕ) × NT ℕ :=
  if memP acc.2 k then acc else (t :: acc.1, insP acc.2 k)

@[expose] def stepW (acc : List (List ℕ) × NT ℕ) (t : List ℕ) : List (List ℕ) × NT ℕ :=
  stepWK acc t (maskOf 0 t)

@[expose] def roundW (fs : List (List ℕ → List ℕ)) (fr : List (List ℕ)) (seen : NT ℕ) :
    List (List ℕ) × NT ℕ :=
  (fr.flatMap fun s => fs.map fun f => f s).foldl stepW ([], seen)

@[expose] def closW (fs : List (List ℕ → List ℕ)) :
    ℕ → List (List ℕ) → NT ℕ → List (List ℕ) → List (List ℕ)
  | 0, fr, _, vis => fr ++ vis
  | fuel + 1, fr, seen, vis =>
    let r := roundW fs fr seen
    if r.1.isEmpty then fr ++ vis else closW fs fuel r.1 r.2 (fr ++ vis)

@[expose] def imgFs : List (List ℕ → List ℕ) := nGensL.map fun A cs => cs.map (mvNR A)

@[expose] def orbW : List (List ℕ) := closW imgFs 100 [w1L] (insP (.tip []) (maskOf 0 w1L)) []

@[expose] def orbAtS (O : List (List ℕ)) (M : List ℕ) (S : NT ℕ) : Bool :=
  Nat.beq M.length 77 && nodupP M &&
    O.all fun cs => nGensL.all fun A => memP S (maskOf 0 (cs.map (mvNR A)))

@[expose] def orbAtM (O : List (List ℕ)) (M : List ℕ) : Bool := orbAtS O M (ofListP M)

@[expose] def ok45Orb : Bool := orbAtM orbW (orbW.map (maskOf 0))

@[expose] def memAll (S : NT ℕ) (ps : List ℕ) : Bool := ps.all fun p => memP S p

@[expose] def ok45Stab : Bool := memAll (ofListP (enumQ stab1Q)) pQ

@[expose] def mapsQ (A : List ℕ) (m : ℕ) (cs : List ℕ) : Bool := cs.all fun c => bitQ m (mvNR A c)

@[expose] def grpAt (gs X : List ℕ) (n : ℕ) : Bool :=
  gensOKQ gs && X.contains oneQ && closedQ gs X && nodupP X && Nat.beq X.length n

@[expose] def pAt (gs : List ℕ) (om : ℕ) (W P : List ℕ) (m : ℕ) : Bool :=
  grpAt gs P 256 && Nat.beq (fixAll gs) 9 &&
    gs.all (fun g => [0, 3, 192, 195].all fun n => [0, 3, 192, 195].contains (mvNR (unpackQ g) n)) &&
    (om :: gs).all fun g => Nat.beq (maskOf 0 (W.map (mvNR (unpackQ g)))) m

@[expose] def ok45P : Bool := pAt pQ omegaQ w1L (enumQ pQ) (maskOf 0 w1L)

@[expose] def ok44Stab : Bool := memAll (ofListP (enumQ stab1Q)) gZQ

@[expose] def grp44At (gs ps S X P : List ℕ) : Bool :=
  grpAt gs X 1920 && grpAt ps P 16 && gs.all (fun g => Nat.beq (mvNR (unpackQ g) 192) 192) &&
    !Nat.beq (mvNR (unpackQ (S.getD 4 oneQ)) 192) 192 && memAll (ofListP X) ps &&
    P.all (fun x => P.all fun y => Nat.beq (mulQ x y) (mulQ y x)) &&
    P.all fun x => Nat.beq (mulQ x x) oneQ

@[expose] def ok44Grp : Bool := grp44At gZQ p2Q stab1Q (enumQ gZQ) (enumQ p2Q)

@[expose] def inW5 (cs : List ℕ) : Bool :=
  let m := maskOf 0 cs
  bitQ m 3 && bitQ m 192 && bitQ m 195

@[expose] def w5At (ps : List ℕ) (W : List (List ℕ × ℕ)) (X : List ℕ) (Ps : NT ℕ) : Bool :=
  Nat.beq W.length 5 && ps.all (fun p => W.all fun mc => mapsQ (unpackQ p) mc.2 mc.1) &&
    X.all fun x => !(W.all fun mc => mapsQ (unpackQ x) mc.2 mc.1) || memP Ps x

@[expose] def ok44W5 : Bool :=
  w5At p2Q ((orbW.filter inW5).map fun cs => (cs, maskOf 0 cs)) (enumQ gZQ) (ofListP (enumQ p2Q))

@[expose] def ok44Perp : Bool :=
  (enumQ p2Q).all fun x => !([4, 24].all fun c => Nat.beq (mvNR (unpackQ x) c) c) || Nat.beq x oneQ

end Certificates.Kernel.AS91K45

end

end

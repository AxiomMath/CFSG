module

public import Certificates.Data.Kernel.AS91K468.K47
public import CFSG.Quasithin.H13.AS91Sec4SixInputs
public import CFSG.Quasithin.H13.AS91Sec4FourInputs

public section

noncomputable section

namespace Certificates.Kernel.AS91K468

open CFSG.KC.Mat12P CFSG.KC.Mat8P Certificates.Kernel.HJ12K

@[expose] def nQ : List ℕ :=
  [11151733896890032821475586019756144924315655, 18143202638049872146410063341699308803141363,
    5365497657942450660064270864226479759481008, 11151733896890032821475586019756144924315655,
    14295200262100043786427221488448615565533260, 4532015868322888836756544095819466405298366]

@[expose] def wordQS (gs w : List ℕ) : ℕ := (w.map fun i => gs.getD i oneQ).foldr mulQ oneQ

@[expose] def st1Q : List ℕ :=
  [9434929166451097896438921821798529162777402, 12213670154771886511627129256773722586737469,
    18006079095044621266145188812148444575686174, 16574495776676400334896268313581167974699302,
    7234812525802977909957055696742283841904641]

@[expose] def g13Q : List ℕ :=
  [7670246783025471861276884212918823023393295, 12497965531953677744723260112291376979175917]

@[expose] def omQ : ℕ := 11325979737014698116079553641009599731990592

@[expose] def wordsOK46 : Bool :=
  CFSG.Quasithin.H13.AS91.Two.stab1Words.map (wordQS nQ) == st1Q &&
    CFSG.Quasithin.H13.AS91.Two.g13Words.map (wordQS nQ) == g13Q

@[expose] def stepN (acc : List ℕ × NT ℕ) (t : ℕ) : List ℕ × NT ℕ :=
  if memP acc.2 t then acc else (t :: acc.1, insP acc.2 t)

@[expose] def roundN (fs : List (ℕ → ℕ)) (fr : List ℕ) (t : NT ℕ) : List ℕ × NT ℕ :=
  (fr.flatMap fun s => fs.map fun f => f s).foldl stepN ([], t)

@[expose] def closN (fs : List (ℕ → ℕ)) : ℕ → List ℕ → NT ℕ → List ℕ → List ℕ
  | 0, fr, _, vis => fr ++ vis
  | fuel + 1, fr, t, vis =>
    let r := roundN fs fr t
    if r.1.isEmpty then fr ++ vis else closN fs fuel r.1 r.2 (fr ++ vis)

@[expose] def w1OK46Q : Bool :=
  (CFSG.Quasithin.H13.AS91.Two.w1List.all fun a =>
    CFSG.Quasithin.H13.AS91.Two.w1List.all fun b => bitQ w1M (a ^^^ b)) &&
    CFSG.Quasithin.H13.AS91.Two.w1List.all fun a => !CFSG.GF2Type.Smith1979.GammaU.q0b a

@[expose] def w1B : List ℕ := [3, 40, 192, 276, 1028, 2560]

@[expose] def spanL : List ℕ → List ℕ
  | [] => [0]
  | b :: B => spanL B ++ (spanL B).map (b ^^^ ·)

@[expose] def fixW1 (x : ℕ) : Bool := w1B.all fun b => Nat.beq (mvNR (unpackQ x) b) b

@[expose] def imgQ (g m : ℕ) : ℕ :=
  (List.range 4096).foldl (fun acc x => if m.testBit x then acc ||| 1 <<< mvNR (unpackQ g) x else acc) 0

@[expose] def ebAt (St P Eb : List ℕ) : Bool :=
  gensOKQ ebQ && ebQ.all fixW1 && ebQ.all (fun e => P.contains e) &&
    ebQ.all (fun e => Nat.beq (mulQ e omQ) (mulQ omQ e)) &&
    Eb.contains oneQ && closedQ ebQ Eb && nodupP Eb && Nat.beq Eb.length 16 &&
    St.all (fun x => !fixW1 x || Eb.contains x) &&
    g13Q.all (fun g => Nat.beq (imgQ g w1M) w1M) &&
    Eb.all (fun x => Eb.all fun y => Nat.beq (mulQ x y) (mulQ y x)) &&
    Eb.all fun x => Nat.beq (mulQ x x) oneQ

@[expose] def conjFs : List (ℕ → ℕ) := g13Q.map fun g x => mulQ g (mulQ x (invQ g))

@[expose] def orbQ : List ℕ :=
  closN conjFs 100 [ebQ.headD oneQ] (insP (.tip []) (ebQ.headD oneQ)) []

@[expose] def transAt (Eb O : List ℕ) : Bool :=
  gensOKQ g13Q && Eb.all fun x => Nat.beq x oneQ || O.contains x

@[expose] def pfOf (P : List ℕ) : List (ℕ × ℕ) := P.map fun x => (x, fixMask (unpackQ x))

@[expose] def fixClQ (PF : List (ℕ × ℕ)) : List ℕ :=
  closN (PF.map fun rf F => F &&& rf.2) 100 [fullM] (insP (.tip []) fullM) []

@[expose] def jFQ (PF : List (ℕ × ℕ)) (m F : ℕ) : Bool :=
  let C := (PF.filter fun rf => F &&& rf.2 == F).map Prod.fst
  let n := C.length * min 64 (CFSG.KC.pc4096 F)
  if F == m then C.length == 16 else
    n ≤ 512 || (n ≤ 1024 && C.length == 64 &&
      C.any fun a => C.any fun b => !Nat.beq (mulQ a b) (mulQ b a))

@[expose] def jAt (PF : List (ℕ × ℕ)) (L : List ℕ) (S : NT ℕ) : Bool :=
  (L.all fun F => PF.all fun rf => memP S (F &&& rf.2)) && L.all (jFQ PF w1M)

@[expose] def jAtL (PF : List (ℕ × ℕ)) : Bool := jAt PF (fixClQ PF) (ofListP (fixClQ PF))

@[expose] def pNodup46Q : Bool := nodupP (enumQ pQ)

@[expose] def eb46Q : Bool := ebAt (enumQ st1Q) (enumQ pQ) (enumQ ebQ)

@[expose] def trans46Q : Bool := transAt (enumQ ebQ) orbQ


end Certificates.Kernel.AS91K468

end

end

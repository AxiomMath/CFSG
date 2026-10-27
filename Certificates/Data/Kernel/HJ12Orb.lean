module

public import Certificates.Data.Kernel.HJ12KT

public section

noncomputable section

namespace Certificates.Kernel.HJ12K

open CFSG.KC.Mat12P CFSG.KC.Mat8P CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12

@[expose] def closedOQ (O : List ℕ) (M : ℕ) : Bool :=
  O.all fun x => bitQ M (mvNR acL x) && bitQ M (mvNR bcL x)

@[expose] def orbAt (O1 O2 : List ℕ) (M1 M2 : ℕ) : Bool :=
  closedOQ O1 M1 && closedOQ O2 M2 && nodupP O1 && Nat.beq O1.length 1575 && nodupP O2 &&
    Nat.beq O2.length 2520 &&
    (List.range 4096).all fun v => Nat.beq v 0 || (bitQ M1 v != bitQ M2 v)

@[expose] def orbQ : Bool :=
  orbAt (orbitQ 4) (orbitQ 1024) (maskOf 0 (orbitQ 4)) (maskOf 0 (orbitQ 1024))

@[expose] def s1At (gs ja X J : List ℕ) : Bool :=
  gensOKQ gs && closedQ gs X && nodupP X && Nat.beq X.length 384 &&
    gs.all (fun g => Nat.beq (mvNR (unpackQ g) 4) 4) &&
    gensOKQ ja && closedQ ja J && nodupP J && Nat.beq J.length 64 &&
    gs.all fun s => ja.all fun j => J.contains (mulQ (mulQ s j) (invQ s))

@[expose] def s1gQ : List ℕ := hj_stab1Words.map wordQ

@[expose] def jaQ : List ℕ := (hj_a1Words ++ hj_a2Words).map wordQ

@[expose] def s1Q : Bool := s1At s1gQ jaQ (enumQ s1gQ) (enumQ jaQ)

@[expose] def ord5Q (ab : ℕ) : Bool := Nat.beq (mulQ (mulQ (mulQ ab ab) (mulQ ab ab)) ab) oneQ

@[expose] def s2At (es ks E K EK : List ℕ) : Bool :=
  gensOKQ (es ++ ks) && closedQ es E && closedQ ks K && closedQ (es ++ ks) EK &&
    nodupP E && Nat.beq E.length 4 && nodupP K && Nat.beq K.length 60 &&
    nodupP EK && Nat.beq EK.length 240 &&
    E.all (fun x => Nat.beq (mulQ x x) oneQ) && E.all (fun x => E.all fun y => commQ x y) &&
    Nat.beq (mulQ (ks.headD oneQ) (ks.headD oneQ)) oneQ &&
    Nat.beq (mulQ (mulQ (ks.getD 1 oneQ) (ks.getD 1 oneQ)) (ks.getD 1 oneQ)) oneQ &&
    ord5Q (mulQ (ks.headD oneQ) (ks.getD 1 oneQ)) &&
    (es ++ ks).all (fun g => Nat.beq (mvNR (unpackQ g) 1024) 1024) &&
    es.all (fun e => ks.all fun k => commQ e k) &&
    E.all fun x => Nat.beq x oneQ || !K.contains x

@[expose] def esQ : List ℕ := hj_eWords.map wordQ

@[expose] def ksQ : List ℕ := hj_stWords.map wordQ

@[expose] def s2Q : Bool := s2At esQ ksQ (enumQ esQ) (enumQ ksQ) (enumQ (esQ ++ ksQ))

@[expose] def gamAt (gs A : List ℕ) (b g x : ℕ) (O : List ℕ) : Bool :=
  gensOKQ gs && closedQ gs A && A.contains b && !Nat.beq b oneQ &&
    Nat.beq (mvNR (unpackQ b) g) g && A.contains x && O.contains (g ^^^ mvNR (unpackQ x) g)

@[expose] def gam2 (O : List ℕ) : Bool :=
  gamAt (hj_a1Words.map wordQ) (enumQ (hj_a1Words.map wordQ)) (wordQ hj_gammaA1full.1)
      hj_gammaA1full.2.1 (wordQ hj_gammaA1full.2.2) O &&
    gamAt (hj_a2Words.map wordQ) (enumQ (hj_a2Words.map wordQ)) (wordQ hj_gammaA2full.1)
      hj_gammaA2full.2.1 (wordQ hj_gammaA2full.2.2) O

@[expose] def gamQ : Bool := gam2 (orbitQ 1024)

end Certificates.Kernel.HJ12K

end

end

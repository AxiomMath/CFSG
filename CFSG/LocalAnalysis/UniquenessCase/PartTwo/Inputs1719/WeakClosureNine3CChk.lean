module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Core

public section

namespace CFSG.LocalAnalysis.WeakClosure81.ChkN

open CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

@[expose] def cinvolN (n : Nat) (a : List Nat) : Bool := cmul a a == List.range n

@[expose] def e4N (n : Nat) (a b : List Nat) : List (List Nat) := [List.range n, a, b, cmul a b]

@[expose] def e8N (n : Nat) (a b c : List Nat) : List (List Nat) :=
  [List.range n, a, b, c, cmul a b, cmul a c, cmul b c, cmul (cmul a b) c]

@[expose] def invsN (n : Nat) (T : List (List Nat)) : List (List Nat) :=
  T.filter fun x => x != List.range n && cinvolN n x

@[expose] def seedCheckIN (n : Nat) (I : List (List Nat)) (Es : List (List (List Nat))) : Bool :=
  I.all fun a => (I.filter (ccomm a)).all fun b => a == b ||
    (Es.any (setEq (e4N n a b)) &&
      ((I.filter (ccomm a)).filter (ccomm b)).all fun c => (e4N n a b).contains c ||
        (Es.any (setEq (e8N n a b c)) &&
          ((I.filter (ccomm a)).filter (ccomm b)).all fun x =>
            !(ccomm c x) || (e8N n a b c).contains x))

@[expose] def seedCheckN (n : Nat) (T : List (List Nat)) (Es : List (List (List Nat))) : Bool :=
  seedCheckIN n (invsN n T) Es

@[expose] def seed2CheckN (n : Nat) (T : List (List Nat)) (Es : List (List (List Nat))) : Bool :=
  (invsN n T).all fun a => Es.any (setEq [List.range n, a])

@[expose] def SubData.okN (n : Nat) (D : SubData) : Bool :=
  D.lit == buildCodes (List.range n) D.gc D.tree && tblCheckC (List.range n) D.gc D.lit D.tbl &&
    nodupB D.lit

@[expose] def KData.checkN (n : Nat) (D : KData) (T : List (List Nat)) : Bool :=
  SubData.okN n D.K && SubData.okN n D.N2 && SubData.okN n D.Np &&
  D.N2.lit.all D.K.lit.contains && D.Np.lit.all D.K.lit.contains &&
  D.N2.gc.all D.K.lit.contains && D.Np.gc.all D.K.lit.contains &&
  normB D.K.lit D.N2.lit && normB D.K.lit D.Np.lit &&
  D.N2.lit.all (fun x => cpow x 8 == List.range n) &&
  D.Np.lit.all (fun x => D.N2.lit.contains (cpow x D.p)) &&
  D.K.lit.all (fun q => D.Np.lit.contains (cpow q 8)) &&
  D.K.lit.contains D.y && cpow D.y D.p == List.range n && D.y != List.range n &&
  (D.p == 3 || D.p == 5) &&
  sylB D.K.lit.length (D.K.lit.filter T.contains).length D.p

@[expose] def invCheckN (n : Nat) (T Tinv : List (List Nat)) : Bool :=
  T.length == Tinv.length && (T.zip Tinv).all (fun hh => cmul hh.1 hh.2 == List.range n) &&
  Tinv.all T.contains

@[expose] def evalWN (n : Nat) (gens : List (List Nat)) (w : List Nat) : List Nat :=
  w.foldl (fun acc i => cmul acc (gens.getD i (List.range n))) (List.range n)

@[expose] def centFreeN (n : Nat) (H Lg : List (List Nat)) : Bool :=
  H.all fun h => h == List.range n || Lg.any fun l => !(ccomm h l)

@[expose] def powList (y : List Nat) (p : Nat) : List (List Nat) := (List.range p).map (cpow y)

@[expose] def conjProd (n : Nat) (T Tinv : List (List Nat)) (y : List Nat)
    (w : List (Nat × Nat)) : List Nat :=
  w.foldl (fun acc ij => cmul acc (cmul (cmul (T.getD ij.1 (List.range n)) (cpow y ij.2))
    (Tinv.getD ij.1 (List.range n)))) (List.range n)

@[expose] def threeCheckN (n : Nat) (T Tinv : List (List Nat)) (y : List Nat)
    (w : List (Nat × Nat)) : Bool :=
  w.all (fun ij => decide (ij.1 < T.length)) &&
    cpow (conjProd n T Tinv y w) 3 == List.range n && conjProd n T Tinv y w != List.range n

@[expose] def movCheckN (n : Nat) (T Tinv Lg : List (List Nat)) (D : KData)
    (E : List (List Nat)) (w : List (Nat × Nat)) : Bool :=
  centFreeN n D.K.lit Lg && E.all (normT D.K.lit) &&
    ((D.K.lit.filter T.contains).any fun s => normT (powList D.y D.p) s && !(ccomm s D.y)) &&
    (D.p == 3 || threeCheckN n T Tinv D.y w)

@[expose] def fixCheckN (T : List (List Nat)) (D : KData) (E : List (List Nat)) : Bool :=
  D.p == 3 && E.all D.K.lit.contains &&
    E.any fun e => D.K.lit.any fun k => (D.K.lit.filter T.contains).all fun s =>
      cmul e k != cmul k s

@[expose] def pairCheckN (n : Nat) (T Lg Gg : List (List Nat)) (x l lw y g gw : List Nat) :
    Bool :=
  evalWN n Lg lw == l && evalWN n Gg gw == g && y.length == n && cmul y l == cmul l x &&
    T.any (fun t => cmul x g == cmul g t) && T.any (fun t => cmul y g == cmul g t) &&
    !(ccomm x y)

@[expose] def movStarCheckN (n : Nat) (T Tinv Lg Es0 : List (List Nat)) (D : KData)
    (E : List (List Nat)) : Bool :=
  D.p == 3 && movCheckN n T Tinv Lg D E [] && Es0.all (normT D.K.lit) &&
    (powList D.y 3).all fun x => Es0.all fun e => D.N2.lit.any fun m =>
      cmul (cmul e x) e == cmul m x

@[expose] def closeCheckN (T Es0 : List (List Nat)) (D : KData) : Bool :=
  D.p == 3 && Es0.all D.N2.lit.contains &&
    T.all fun t => D.K.lit.contains t || Es0.any fun e => !(ccomm t e)

structure CEntry where
  E : List (List Nat)
  mov : Nat
  three : List (Nat × Nat)
  fix : Nat
  nrm : Nat
  pl : List Nat
  plw : List Nat
  py : List Nat
  pg : List Nat
  pgw : List Nat
  star : Nat

@[expose] def entryCheckN (n : Nat) (T Tinv Lg Gg Es0 : List (List Nat)) (Ks : List KData)
    (hasStar : Bool) (en : CEntry) : Bool :=
  en.E.all T.contains && decide (en.mov < Ks.length) && decide (en.fix < Ks.length) &&
    decide (en.star < Ks.length) &&
    movCheckN n T Tinv Lg (Ks.getD en.mov KData.dflt) en.E en.three &&
    ((hasStar && setEq en.E Es0) || fixCheckN T (Ks.getD en.fix KData.dflt) en.E) &&
    ((en.nrm == 0 && nonNormal T Tinv en.E) || (en.nrm == 1 && hasStar && setEq en.E Es0) ||
      (en.nrm == 2 && en.E.length == 2 &&
        en.E.all (fun x => x == List.range n ||
          pairCheckN n T Lg Gg x en.pl en.plw en.py en.pg en.pgw))) &&
    (!hasStar || (en.E.any fun e => Es0.any fun s => !(ccomm e s)) ||
      movStarCheckN n T Tinv Lg Es0 (Ks.getD en.star KData.dflt) en.E)

structure ModelData where
  T : List (List Nat)
  Tinv : List (List Nat)
  Lg : List (List Nat)
  Gg : List (List Nat)
  Ks : List KData
  KwG : List (List (List Nat))
  KwL : List (List (List Nat))
  Es : List CEntry
  botMov : Nat
  botThree : List (Nat × Nat)
  Es0 : List (List Nat)
  sqD : List Nat
  sqW : List Nat
  botStar : Nat
  cls : Nat
  clsGens : List (List Nat)
  clsW : List (List Nat)

@[expose] def witOkN (n : Nat) (M : ModelData) (i : Nat) : Bool :=
  KData.checkN n (M.Ks.getD i KData.dflt) M.T &&
    (M.Ks.getD i KData.dflt).K.gc == (M.KwG.getD i []).map (evalWN n M.Gg) &&
    ((M.KwL.getD i []).isEmpty ||
      (M.Ks.getD i KData.dflt).K.gc == (M.KwL.getD i []).map (evalWN n M.Lg))

@[expose] def entOkN (n : Nat) (M : ModelData) (en : CEntry) : Bool :=
  entryCheckN n M.T M.Tinv M.Lg M.Gg M.Es0 M.Ks (!M.Es0.isEmpty) en &&
    !(M.KwL.getD en.mov []).isEmpty &&
    (M.Es0.isEmpty || (en.E.any fun e => M.Es0.any fun s => !(ccomm e s)) ||
      !(M.KwL.getD en.star []).isEmpty)

@[expose] def seedOkN (n : Nat) (M : ModelData) : Bool :=
  seedCheckN n M.T (M.Es.map CEntry.E) && seed2CheckN n M.T (M.Es.map CEntry.E)

@[expose] def botOkN (n : Nat) (M : ModelData) : Bool :=
  decide (M.botMov < M.Ks.length) && !(M.KwL.getD M.botMov []).isEmpty &&
    movCheckN n M.T M.Tinv M.Lg (M.Ks.getD M.botMov KData.dflt) [] M.botThree

@[expose] def sqOkN (n : Nat) (M : ModelData) : Bool :=
  M.T.contains M.sqD && evalWN n M.Lg M.sqW == M.sqD && cpow M.sqD 2 != List.range n

@[expose] def starOkN (n : Nat) (M : ModelData) : Bool :=
  M.Es0.contains (List.range n) &&
    M.Es0.all (fun a => M.T.contains a && cinvolN n a &&
      M.Es0.all fun b => ccomm a b && M.Es0.contains (cmul a b)) &&
    M.T.all (normT M.Es0) &&
    decide (M.botStar < M.Ks.length) && !(M.KwL.getD M.botStar []).isEmpty &&
    movStarCheckN n M.T M.Tinv M.Lg M.Es0 (M.Ks.getD M.botStar KData.dflt) [] &&
    decide (M.cls < M.Ks.length) && closeCheckN M.T M.Es0 (M.Ks.getD M.cls KData.dflt) &&
    M.clsGens.all (fun c => (M.Ks.getD M.cls KData.dflt).K.lit.contains c || M.T.contains c) &&
    M.Gg == M.clsW.map (evalWN n M.clsGens)

end CFSG.LocalAnalysis.WeakClosure81.ChkN

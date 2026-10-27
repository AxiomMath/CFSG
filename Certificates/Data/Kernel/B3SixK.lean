module

public import CFSG.Quasithin.Background.B3FourData
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B3VMod

public section

namespace CFSG.KC.B3Six

open CFSG.Quasithin.B3

@[expose] def pAux : ℕ → List ℕ → List ℕ → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | f + 1, t :: ts, is =>
      List.foldr (fun y r => (List.permutationsAux2 t ts r y id).2) (pAux f ts (t :: is))
        (is :: pAux f is [])

@[expose] def permsK (l : List ℕ) : List (List ℕ) := l :: pAux (l.length ^ 2 + l.length + 1) l []

@[expose] def sym6K : List Tab := permsK (List.range 6)

@[expose] def dedupF (seen : List Tab) : List Tab → List Tab
  | [] => []
  | x :: xs => if seen.contains x then dedupF seen xs else x :: dedupF (x :: seen) xs

@[expose] def closeTK (n : ℕ) (gens : List Tab) : List Tab := closeT n (dedupF [] gens)

@[expose] def chkGenTabsK (n : ℕ) (gens : List Tab) : Bool := chkGenTabs n (dedupF [] gens)

@[expose] def subOfMask {α : Type} : List α → ℕ → List α
  | [], _ => []
  | x :: xs, m => if m % 2 = 1 then x :: subOfMask xs (m / 2) else subOfMask xs (m / 2)

@[expose] def HlX (P : List Tab) (b : Bool) : List Tab := if b then P else P.filter isEvenT

@[expose] def flagCX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool := cmask n k (HlX P b)

@[expose] def flagF1X (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool :=
  fmask n (Tgl n b) (flagCX P n k b)

@[expose] def flagF2X (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool :=
  fmask n (Tgl n b) (flagF1X P n k b)

@[expose] def flagTabsX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) :
    List Bool × List Bool × List Bool :=
  let T := Tgl n b
  let tC := tabOf n (flagCX P n k b)
  let tF1 := tabOf n (fmask n T (lkM n tC (flagCX P n k b)))
  let tF2 := tabOf n (fmask n T (lkM n tF1 (flagF1X P n k b)))
  (tC, tF1, tF2)

@[expose] def flagOKX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : Bool :=
  let tabs := flagTabsX P n k b
  cntT n k tabs.2.1 == 2 * cntT n k tabs.1 && cntT n k tabs.2.2 == 2 * cntT n k tabs.2.1

@[expose] def H1tabX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : List Tab :=
  let tabs := flagTabsX P n k b
  stabTab n k (HlX P b) (lkM n tabs.2.1 (flagF1X P n k b))

@[expose] def H2tabX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : List Tab :=
  let tabs := flagTabsX P n k b
  stabTab n k (HlX P b) (lkM n tabs.2.2 (flagF2X P n k b))

@[expose] def fourDX (P : List Tab) (k : Mod) (b : Bool) : FourD :=
  let n := 6
  let T := Tgl n b
  let H1 := H1tabX P n k b
  let H2 := H2tabX P n k b
  { T := T
    H1 := H1
    H2 := H2
    R1 := rTab H1 T
    R2 := rTab H2 T
    L1 := H1.filter isEvenT
    L2T := closeTK n ((H2.filter isEvenT) ++ T)
    L1d := closeTK n (commGens (H1.filter isEvenT) (H1.filter isEvenT))
    A1p := closeT n [tab (ti n 2)]
    w := cntF n k [idT n] }

@[expose] def jOfK (n : ℕ) (B : List Tab) (S : List (List Tab)) : List Tab :=
  closeTK n ((S.filter (fun K => subsetT K B)).flatten)

@[expose] def jOKK (n : ℕ) (B : List Tab) (S : List (List Tab)) : Bool :=
  chkGenTabsK n ((S.filter (fun K => subsetT K B)).flatten)

@[expose] def claimsGK (k : Mod) (d : FourD) (S : List (List Tab)) : Bool :=
  let n := 6
  let JT := jOfK n d.T S
  let JR1 := jOfK n d.R1 S
  jOKK n d.T S && jOKK n d.R1 S &&
  chkGenTabsK n (commGens d.L1 JT) &&
  subsetT JT d.L2T &&
  (!(S.all (fun K => decide (d.w < Fval n k K))) || (seteqT JR1 [idT n] && seteqT JT d.R2)) &&
  (!(seteqT JR1 [idT n]) ||
    (normalizesT d.L2T JT && seteqT (closeTK n (commGens d.L1 JT)) d.L1d)) &&
  (seteqT JR1 [idT n] || (seteqT (closeTK n (commGens d.L1 JT)) d.L1d &&
    ((seteqT JR1 d.A1p && normalizesT d.L2T JT) || (seteqT JR1 d.R1 && seteqT JT d.T))))

@[expose] def claimsLK (d : FourD) (S : List (List Tab)) : Bool :=
  let n := 6
  jOKK n d.T S && jOKK n d.R1 S && seteqT (jOfK n d.T S) d.R2 && seteqT (jOfK n d.R1 S) [idT n]

@[expose] def chkStruct6X (P : List Tab) (k : Mod) (b : Bool) (e : ℕ) : Bool :=
  let n := 6
  let d := fourDX P k b
  subOK n (Tl n) && chkEA n (Tl n) (Dl n) && subOK n d.T && d.T.length == 2 ^ e &&
    d.T.all (fun t => (Tl n).contains t) && subsetT d.T (HlX P b) &&
    flagOKX P n k b && subOK n d.H1 && subOK n d.H2 && subsetT d.T d.H1 && subsetT d.T d.H2 &&
    d.H1.length == 3 * 2 ^ e && d.H2.length == 3 * 2 ^ e && subOK n d.R1 && subOK n d.R2

@[expose] def chkGenG6X (P : List Tab) (k : Mod) : Bool :=
  let n := 6
  let d := fourDX P k true
  subOK n d.L1 && subOK n (d.H2.filter isEvenT) && chkGenTabsK n (d.H2.filter isEvenT ++ d.T) &&
    chkGenTabsK n (commGens d.L1 d.L1) && chkGenTabs n [tab (ti n 2)]

@[expose] def stableIdx (nbi : List (List ℕ)) (m : ℕ) : Bool :=
  (List.range nbi.length).all (fun i => !m.testBit i || (nbi.getD i []).all (fun j => m.testBit j))

@[expose] def wG6 : List (ℕ × ℕ × Tab) :=
  [(0, 1, [2, 3, 5, 4, 1, 0]), (0, 2, [3, 2, 1, 0, 4, 5]), (1, 0, [5, 0, 4, 1, 2, 3]),
   (1, 2, [5, 4, 3, 2, 1, 0]), (2, 0, [3, 2, 1, 0, 4, 5]), (2, 1, [5, 4, 3, 2, 1, 0]),
   (3, 5, [3, 2, 1, 0, 4, 5]), (3, 7, [2, 3, 5, 4, 1, 0]), (4, 8, [1, 0, 2, 3, 4, 5]),
   (4, 9, [5, 0, 4, 1, 2, 3]), (4, 10, [1, 2, 0, 3, 4, 5]), (4, 11, [4, 3, 5, 2, 1, 0]),
   (5, 3, [3, 2, 1, 0, 4, 5]), (5, 7, [5, 4, 3, 2, 1, 0]), (7, 3, [5, 4, 0, 1, 2, 3]),
   (7, 5, [5, 4, 3, 2, 1, 0]), (8, 4, [1, 0, 2, 3, 4, 5]), (8, 9, [0, 5, 4, 1, 2, 3]),
   (8, 10, [2, 1, 0, 3, 4, 5]), (8, 11, [4, 3, 2, 5, 1, 0]), (9, 4, [1, 3, 5, 4, 2, 0]),
   (9, 8, [1, 2, 5, 4, 3, 0]), (9, 10, [2, 3, 5, 4, 1, 0]), (9, 11, [3, 2, 1, 0, 4, 5]),
   (10, 4, [2, 0, 1, 3, 4, 5]), (10, 8, [2, 1, 0, 3, 4, 5]), (10, 9, [5, 4, 0, 1, 2, 3]),
   (10, 11, [5, 4, 3, 2, 1, 0]), (11, 4, [5, 4, 1, 3, 2, 0]), (11, 8, [5, 4, 1, 2, 3, 0]),
   (11, 9, [3, 2, 1, 0, 4, 5]), (11, 10, [5, 4, 3, 2, 1, 0])]

@[expose] def nbIdxF (len : ℕ) (e : ℕ → ℕ → Bool) : List (List ℕ) :=
  (List.range len).map (fun i => (List.range len).filter (e i))

@[expose] def edgeW (X : List Tab) (n : ℕ) (k : Mod) (offs : List (List Tab))
    (W : List (ℕ × ℕ × Tab)) (i j : ℕ) : Bool :=
  lesB n k (offs.getD i []) (offs.getD j []) ||
    W.any (fun w => w.1 == i && w.2.1 == j && X.contains w.2.2 &&
      seteqT (conjT w.2.2 (offs.getD i [])) (offs.getD j []))

@[expose] def chkSubG6X (P : List Tab) (W : List (ℕ × ℕ × Tab)) (k : Mod) : Bool :=
  let n := 6
  let d := fourDX P k true
  let offs := offsH n k true
  let nbi := nbIdxF offs.length (edgeW (HlX P true) n k offs W)
  decide offs.Nodup && (List.range (2 ^ offs.length)).all (fun m =>
    !stableIdx nbi m || (fun S => S.isEmpty || claimsGK k d S) (subOfMask offs m))

@[expose] def chkWitG6X (P : List Tab) (k : Mod) : Bool :=
  let n := 6
  let d := fourDX P k true
  (offsH n k true).all (fun K => K.length == 2 || witB (HlX P true) (Dl n) d.T d.R2 K)

@[expose] def chkRG6X (P : List Tab) (k : Mod) : Bool :=
  let n := 6
  let d := fourDX P k true
  seteqT d.R2 (Dc n) && !(subsetT (Dc n) d.R1)

@[expose] def chkG6X (P : List Tab) (W : List (ℕ × ℕ × Tab)) (k : Mod) : Bool :=
  chkStruct6X P k true 4 && chkGenG6X P k && chkSubG6X P W k && chkWitG6X P k && chkRG6X P k

@[expose] def chkSubL6X (P : List Tab) (k : Mod) : Bool :=
  let n := 6
  let d := fourDX P k false
  let offs := offsH n k false
  let nbi := nbIdxF offs.length (fun i j =>
    (nbrK n k (HlX P false) offs (offs.getD i [])).contains (offs.getD j []))
  decide offs.Nodup && (List.range (2 ^ offs.length)).all (fun m =>
    !stableIdx nbi m || (fun S => S.isEmpty || claimsLK d S) (subOfMask offs m))

@[expose] def chkRL6X (P : List Tab) (k : Mod) : Bool :=
  let n := 6
  let d := fourDX P k false
  d.R2.length == 4 &&
    (offsH n k false).all (fun K => !(subsetT K d.R2) || !(decide (d.w < Fval n k K)))

@[expose] def chkL6X (P : List Tab) (k : Mod) : Bool :=
  chkStruct6X P k false 3 && chkSubL6X P k && chkRL6X P k

@[expose] def elemAbTK (n : ℕ) (A : List Tab) : Bool :=
  A.all (fun x => A.all (fun y => mulT x y == mulT y x)) && A.all (fun x => mulT x x == idT n)

@[expose] def chkEA6X (P : List Tab) (k : Mod) : Bool :=
  elemAbTK 6 (fourDX P k false).R2 && elemAbTK 6 (fourDX P k true).R2

@[expose] def chkLit6X (P : List Tab) (k : Mod) : Bool :=
  let d := fourDX P k true
  chkGenTabsK 6 (commGens d.L1 d.H1) && decide ((closeTK 6 (commGens d.L1 d.H1)).length < d.L1.length)

end CFSG.KC.B3Six

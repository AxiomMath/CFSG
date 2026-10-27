module

public import CFSG.Quasithin.Background.B3Chk

public section

namespace CFSG.Quasithin.B3

@[expose] def allTabs (n : ℕ) : List Tab := (List.range n).permutations

@[expose] def evenTabs (n : ℕ) : List Tab := (allTabs n).filter isEvenT

@[expose] def Hl (n : ℕ) (b : Bool) : List Tab := if b then allTabs n else evenTabs n

@[expose] def Tgl (n : ℕ) (b : Bool) : List Tab := if b then Tl n else (Tl n).filter isEvenT

@[expose] def cmask (n : ℕ) (k : Mod) (X : List Tab) (m : ℕ) : Bool :=
  X.all (fun h => inNk n k (actM n h m ^^^ m))

@[expose] def fmask (n : ℕ) (T : List Tab) (p : ℕ → Bool) (m : ℕ) : Bool :=
  T.all (fun t => p (actM n t m ^^^ m))

@[expose] def cntS (n : ℕ) (k : Mod) (p : ℕ → Bool) : ℕ :=
  ((List.range (2 ^ n)).filter (fun m => inWk n k m && p m)).length

@[expose] def stabTab (n : ℕ) (k : Mod) (X : List Tab) (p : ℕ → Bool) : List Tab :=
  X.filter (fun h => (List.range (2 ^ n)).all (fun m => !inWk n k m || (p m == p (actM n h m))))

@[expose] def tabOf (n : ℕ) (p : ℕ → Bool) : List Bool := (List.range (2 ^ n)).map p

@[expose] def lkM (n : ℕ) (t : List Bool) (p : ℕ → Bool) (m : ℕ) : Bool :=
  if m < 2 ^ n then t.getD m false else p m

theorem lkM_tabOf (n : ℕ) (p : ℕ → Bool) (m : ℕ) : lkM n (tabOf n p) p m = p m := by
  unfold lkM tabOf
  by_cases h : m < 2 ^ n
  · simp [h, List.getD_eq_getElem?_getD]
  · simp [h]

@[expose] def flagC (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool := cmask n k (Hl n b)

@[expose] def flagF1 (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool :=
  fmask n (Tgl n b) (flagC n k b)

@[expose] def flagF2 (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool :=
  fmask n (Tgl n b) (flagF1 n k b)

@[expose] def flagTabs (n : ℕ) (k : Mod) (b : Bool) : List Bool × List Bool × List Bool :=
  let T := Tgl n b
  let tC := tabOf n (flagC n k b)
  let tF1 := tabOf n (fmask n T (lkM n tC (flagC n k b)))
  let tF2 := tabOf n (fmask n T (lkM n tF1 (flagF1 n k b)))
  (tC, tF1, tF2)

theorem flagTabs_spec (n : ℕ) (k : Mod) (b : Bool) :
    (flagTabs n k b).1 = tabOf n (flagC n k b) ∧ (flagTabs n k b).2.1 = tabOf n (flagF1 n k b) ∧
      (flagTabs n k b).2.2 = tabOf n (flagF2 n k b) := by
  have hC : lkM n (tabOf n (flagC n k b)) (flagC n k b) = flagC n k b :=
    funext (lkM_tabOf n _)
  have hF1 : tabOf n (fmask n (Tgl n b) (lkM n (tabOf n (flagC n k b)) (flagC n k b))) =
      tabOf n (flagF1 n k b) := by
    rw [hC]
    rfl
  refine ⟨rfl, hF1, ?_⟩
  unfold flagTabs
  simp only
  rw [hF1]
  have : lkM n (tabOf n (flagF1 n k b)) (flagF1 n k b) = flagF1 n k b := funext (lkM_tabOf n _)
  rw [this]
  rfl

@[expose] def cntT (n : ℕ) (k : Mod) (t : List Bool) : ℕ :=
  ((List.range (2 ^ n)).filter (fun m => inWk n k m && t.getD m false)).length

theorem cntT_tabOf (n : ℕ) (k : Mod) (p : ℕ → Bool) : cntT n k (tabOf n p) = cntS n k p := by
  unfold cntT cntS tabOf
  congr 1
  apply List.filter_congr
  intro m hm
  have hm' : m < 2 ^ n := List.mem_range.1 hm
  simp [hm', List.getD_eq_getElem?_getD]

@[expose] def flagOK (n : ℕ) (k : Mod) (b : Bool) : Bool :=
  let tabs := flagTabs n k b
  cntT n k tabs.2.1 == 2 * cntT n k tabs.1 && cntT n k tabs.2.2 == 2 * cntT n k tabs.2.1

@[expose] def H1tab (n : ℕ) (k : Mod) (b : Bool) : List Tab :=
  let tabs := flagTabs n k b
  stabTab n k (Hl n b) (lkM n tabs.2.1 (flagF1 n k b))

@[expose] def H2tab (n : ℕ) (k : Mod) (b : Bool) : List Tab :=
  let tabs := flagTabs n k b
  stabTab n k (Hl n b) (lkM n tabs.2.2 (flagF2 n k b))

theorem H1tab_eq (n : ℕ) (k : Mod) (b : Bool) : H1tab n k b = stabTab n k (Hl n b) (flagF1 n k b) := by
  unfold H1tab
  simp only
  rw [(flagTabs_spec n k b).2.1]
  have : lkM n (tabOf n (flagF1 n k b)) (flagF1 n k b) = flagF1 n k b := funext (lkM_tabOf n _)
  rw [this]

theorem H2tab_eq (n : ℕ) (k : Mod) (b : Bool) : H2tab n k b = stabTab n k (Hl n b) (flagF2 n k b) := by
  unfold H2tab
  simp only
  rw [(flagTabs_spec n k b).2.2]
  have : lkM n (tabOf n (flagF2 n k b)) (flagF2 n k b) = flagF2 n k b := funext (lkM_tabOf n _)
  rw [this]

@[expose] def rTab (X T : List Tab) : List Tab :=
  T.filter (fun r => X.all (fun x => T.contains (mulT (mulT (invT x) r) x)))

@[expose] def subsetT (A B : List Tab) : Bool := A.all (fun a => B.contains a)

@[expose] def commT (a b : Tab) : Tab := mulT (mulT a b) (mulT (invT a) (invT b))

@[expose] def commGens (A B : List Tab) : List Tab := A.flatMap (fun a => B.map (commT a))

@[expose] def commSub (n : ℕ) (A B : List Tab) : List Tab := closeT n (commGens A B)

@[expose] def normalizesT (X J : List Tab) : Bool :=
  X.all (fun x => J.all (fun j => J.contains (cjT x j)))

@[expose] def offsK (n : ℕ) (k : Mod) : List (List Tab) :=
  let DF := mkDF n k (Dl n)
  (Dl n).filter (fun K => offP DF (K, Fval n k K))

@[expose] def offsH (n : ℕ) (k : Mod) (b : Bool) : List (List Tab) :=
  (offsK n k).filter (fun K => subsetT K (Tgl n b))

@[expose] def fusB (X : List Tab) (K K' : List Tab) : Bool :=
  X.any (fun g => seteqT (conjT g K) K')

@[expose] def lesB (n : ℕ) (k : Mod) (K K' : List Tab) : Bool :=
  subsetT K' K && Fval n k K' == Fval n k K

@[expose] def nbrK (n : ℕ) (k : Mod) (X : List Tab) (offs : List (List Tab)) (K : List Tab) :
    List (List Tab) :=
  offs.filter (fun K' => fusB X K K' || lesB n k K K')

@[expose] def nbrTab (n : ℕ) (k : Mod) (X : List Tab) (offs : List (List Tab)) :
    List (List Tab × List (List Tab)) :=
  offs.map (fun K => (K, nbrK n k X offs K))

@[expose] def stableB (NB : List (List Tab × List (List Tab))) (S : List (List Tab)) : Bool :=
  S.all (fun K => ((NB.lookup K).getD []).all (fun K' => S.contains K'))

@[expose] def jOf (n : ℕ) (B : List Tab) (S : List (List Tab)) : List Tab :=
  closeT n ((S.filter (fun K => subsetT K B)).flatten)

@[expose] def jOK (n : ℕ) (B : List Tab) (S : List (List Tab)) : Bool :=
  chkGenTabs n ((S.filter (fun K => subsetT K B)).flatten)

structure FourD where
  T : List Tab
  H1 : List Tab
  H2 : List Tab
  R1 : List Tab
  R2 : List Tab
  L1 : List Tab
  L2T : List Tab
  L1d : List Tab
  A1p : List Tab
  w : ℕ

@[expose] def fourD (k : Mod) (b : Bool) : FourD :=
  let n := 6
  let T := Tgl n b
  let H1 := H1tab n k b
  let H2 := H2tab n k b
  { T := T
    H1 := H1
    H2 := H2
    R1 := rTab H1 T
    R2 := rTab H2 T
    L1 := H1.filter isEvenT
    L2T := closeT n ((H2.filter isEvenT) ++ T)
    L1d := commSub n (H1.filter isEvenT) (H1.filter isEvenT)
    A1p := closeT n [tab (ti n 2)]
    w := cntF n k [idT n] }

@[expose] def claimsG (k : Mod) (d : FourD) (S : List (List Tab)) : Bool :=
  let n := 6
  let JT := jOf n d.T S
  let JR1 := jOf n d.R1 S
  jOK n d.T S && jOK n d.R1 S &&
  chkGenTabs n (commGens d.L1 JT) &&
  subsetT JT d.L2T &&
  (!(S.all (fun K => decide (d.w < Fval n k K))) || (seteqT JR1 [idT n] && seteqT JT d.R2)) &&
  (!(seteqT JR1 [idT n]) ||
    (normalizesT d.L2T JT && seteqT (commSub n d.L1 JT) d.L1d)) &&
  (seteqT JR1 [idT n] || (seteqT (commSub n d.L1 JT) d.L1d &&
    ((seteqT JR1 d.A1p && normalizesT d.L2T JT) || (seteqT JR1 d.R1 && seteqT JT d.T))))

@[expose] def witB (X : List Tab) (D : List (List Tab)) (T R2 : List Tab) (K : List Tab) : Bool :=
  X.any (fun g => D.any (fun B =>
    subsetT B T && 2 * B.length == K.length && !(subsetT B R2) && subsetT B (conjT g K)))

@[expose] def chkStruct6 (k : Mod) (b : Bool) (e : ℕ) : Bool :=
  let n := 6
  let d := fourD k b
  subOK n (Tl n) && chkEA n (Tl n) (Dl n) && subOK n d.T && d.T.length == 2 ^ e &&
    d.T.all (fun t => (Tl n).contains t) && subsetT d.T (Hl n b) &&
    flagOK n k b && subOK n d.H1 && subOK n d.H2 && subsetT d.T d.H1 && subsetT d.T d.H2 &&
    d.H1.length == 3 * 2 ^ e && d.H2.length == 3 * 2 ^ e && subOK n d.R1 && subOK n d.R2

@[expose] def chkGenG6 (k : Mod) : Bool :=
  let n := 6
  let d := fourD k true
  subOK n d.L1 && subOK n (d.H2.filter isEvenT) && chkGenTabs n (d.H2.filter isEvenT ++ d.T) &&
    chkGenTabs n (commGens d.L1 d.L1) && chkGenTabs n [tab (ti n 2)]

@[expose] def chkSubG6 (k : Mod) : Bool :=
  let n := 6
  let d := fourD k true
  let offs := offsH n k true
  let NB := nbrTab n k (Hl n true) offs
  (offs.sublists.filter (stableB NB)).all (fun S => S.isEmpty || claimsG k d S)

@[expose] def chkWitG6 (k : Mod) : Bool :=
  let n := 6
  let d := fourD k true
  (offsH n k true).all (fun K => K.length == 2 || witB (Hl n true) (Dl n) d.T d.R2 K)

@[expose] def chkRG6 (k : Mod) : Bool :=
  let n := 6
  let d := fourD k true
  seteqT d.R2 (Dc n) && !(subsetT (Dc n) d.R1)

@[expose] def chkG6 (k : Mod) : Bool :=
  chkStruct6 k true 4 && chkGenG6 k && chkSubG6 k && chkWitG6 k && chkRG6 k

@[expose] def claimsL (d : FourD) (S : List (List Tab)) : Bool :=
  let n := 6
  jOK n d.T S && jOK n d.R1 S && seteqT (jOf n d.T S) d.R2 && seteqT (jOf n d.R1 S) [idT n]

@[expose] def chkSubL6 (k : Mod) : Bool :=
  let n := 6
  let d := fourD k false
  let offs := offsH n k false
  let NB := nbrTab n k (Hl n false) offs
  (offs.sublists.filter (stableB NB)).all (fun S => S.isEmpty || claimsL d S)

@[expose] def chkRL6 (k : Mod) : Bool :=
  let n := 6
  let d := fourD k false
  d.R2.length == 4 &&
    (offsH n k false).all (fun K => !(subsetT K d.R2) || !(decide (d.w < Fval n k K)))

@[expose] def chkL6 (k : Mod) : Bool :=
  chkStruct6 k false 3 && chkSubL6 k && chkRL6 k

end CFSG.Quasithin.B3

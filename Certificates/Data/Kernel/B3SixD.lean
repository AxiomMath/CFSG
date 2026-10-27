module

public import Certificates.Data.Kernel.B3SixK

public section

namespace CFSG.KC.B3Six

open CFSG.Quasithin.B3

@[expose] def eqD (d e : FourD) : Bool :=
  d.T == e.T && d.H1 == e.H1 && d.H2 == e.H2 && d.R1 == e.R1 && d.R2 == e.R2 && d.L1 == e.L1 &&
    d.L2T == e.L2T && d.L1d == e.L1d && d.A1p == e.A1p && d.w == e.w

@[expose] noncomputable def codeT (t : Tab) : ℕ :=
  t.rec (motive := fun _ => ℕ) 0 (fun a _ r => a + 8 * r)

@[expose] noncomputable def memN (c : ℕ) (C : List ℕ) : Bool :=
  C.rec (motive := fun _ => Bool) false (fun x _ r => Nat.beq c x || r)

@[expose] noncomputable def subOKN (S : List Tab) : Bool :=
  let C := S.map codeT
  S.all (isTab 6) && memN (codeT (idT 6)) C &&
    S.all (fun a => S.all (fun b => memN (codeT (mulT a b)) C)) &&
    S.all (fun a => memN (codeT (invT a)) C) && decide S.Nodup

@[expose] noncomputable def chkGenTabsS (gens S : List Tab) : Bool :=
  subOKN S && (dedupF [] gens).all (fun g => S.contains g) && chainOK (dedupF [] gens) (idT 6) [] S

@[expose] noncomputable def chkGenTabsN (gens : List Tab) : Bool := chkGenTabsS gens (closeTK 6 gens)

@[expose] noncomputable def jOKN (B : List Tab) (S : List (List Tab)) : Bool :=
  chkGenTabsN ((S.filter (fun K => subsetT K B)).flatten)

@[expose] noncomputable def claimsGN (k : Mod) (d : FourD) (S : List (List Tab)) : Bool :=
  let n := 6
  let JT := jOfK n d.T S
  let JR1 := jOfK n d.R1 S
  jOKN d.T S && jOKN d.R1 S &&
  chkGenTabsN (commGens d.L1 JT) &&
  subsetT JT d.L2T &&
  (!(S.all (fun K => decide (d.w < Fval n k K))) || (seteqT JR1 [idT n] && seteqT JT d.R2)) &&
  (!(seteqT JR1 [idT n]) ||
    (normalizesT d.L2T JT && seteqT (closeTK n (commGens d.L1 JT)) d.L1d)) &&
  (seteqT JR1 [idT n] || (seteqT (closeTK n (commGens d.L1 JT)) d.L1d &&
    ((seteqT JR1 d.A1p && normalizesT d.L2T JT) || (seteqT JR1 d.R1 && seteqT JT d.T))))

@[expose] noncomputable def claimsLN (d : FourD) (S : List (List Tab)) : Bool :=
  let n := 6
  jOKN d.T S && jOKN d.R1 S && seteqT (jOfK n d.T S) d.R2 && seteqT (jOfK n d.R1 S) [idT n]

@[expose] noncomputable def chkStruct6D (P : List Tab) (d : FourD) (k : Mod) (b : Bool) (e : ℕ) :
    Bool :=
  let n := 6
  subOKN (Tl n) && chkEA n (Tl n) (Dl n) && subOKN d.T && d.T.length == 2 ^ e &&
    d.T.all (fun t => (Tl n).contains t) && subsetT d.T (HlX P b) &&
    flagOKX P n k b && subOKN d.H1 && subOKN d.H2 && subsetT d.T d.H1 && subsetT d.T d.H2 &&
    d.H1.length == 3 * 2 ^ e && d.H2.length == 3 * 2 ^ e && subOKN d.R1 && subOKN d.R2

@[expose] noncomputable def chkGenG6D (d : FourD) : Bool :=
  let n := 6
  subOKN d.L1 && subOKN (d.H2.filter isEvenT) &&
    chkGenTabsS (d.H2.filter isEvenT ++ d.T) d.L2T &&
    chkGenTabsS (commGens d.L1 d.L1) d.L1d && chkGenTabs n [tab (ti n 2)]

@[expose] noncomputable def chkSubG6D (P : List Tab) (W : List (ℕ × ℕ × Tab)) (d : FourD)
    (k : Mod) : Bool :=
  let n := 6
  let offs := offsH n k true
  let nbi := nbIdxF offs.length (edgeW (HlX P true) n k offs W)
  decide offs.Nodup && (List.range (2 ^ offs.length)).all (fun m =>
    !stableIdx nbi m || (fun S => S.isEmpty || claimsGN k d S) (subOfMask offs m))

@[expose] def chkWitG6D (P : List Tab) (d : FourD) (k : Mod) : Bool :=
  let n := 6
  (offsH n k true).all (fun K => K.length == 2 || witB (HlX P true) (Dl n) d.T d.R2 K)

@[expose] def chkRG6D (d : FourD) : Bool :=
  let n := 6
  seteqT d.R2 (Dc n) && !(subsetT (Dc n) d.R1)

@[expose] noncomputable def chkSubL6D (P : List Tab) (d : FourD) (k : Mod) : Bool :=
  let n := 6
  let offs := offsH n k false
  let nbi := nbIdxF offs.length (fun i j =>
    (nbrK n k (HlX P false) offs (offs.getD i [])).contains (offs.getD j []))
  decide offs.Nodup && (List.range (2 ^ offs.length)).all (fun m =>
    !stableIdx nbi m || (fun S => S.isEmpty || claimsLN d S) (subOfMask offs m))

@[expose] def chkRL6D (d : FourD) (k : Mod) : Bool :=
  let n := 6
  d.R2.length == 4 &&
    (offsH n k false).all (fun K => !(subsetT K d.R2) || !(decide (d.w < Fval n k K)))

end CFSG.KC.B3Six

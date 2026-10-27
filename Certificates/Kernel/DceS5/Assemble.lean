module

public import Certificates.Data.Kernel.DceS5
public import Certificates.Kernel.DceSP.Assemble
public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.AddThm

open Lean Elab Command

public section

namespace CFSG.Certificates.DS5

open CFSG.KC.LyA.DceS CFSG.Certificates.LCE

theorem andB_intro' {a b : Bool} (ha : a = true) (hb : b = true) : andB a b = true := by
  rw [ha, hb]
  rfl

theorem andB_right' {a b : Bool} (h : andB a b = true) : b = true := by
  cases a
  · exact absurd h (by simp [andB])
  · exact h

theorem runFacts_append (FB HB GB TB WD : Nat → Nat) (sh wd LT TL VL NL ND NO nH nT nW W Wi : Nat)
    (l1 l2 : List Nat) (x : Nat) :
    runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi (List.append l1 l2) x =
      runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi l2
        (runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi l1 x) :=
  chunkLoop_append (fun C S => runChunk FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi C S)
    l1 l2 x

theorem runHdr_append (HB : Nat → Nat) (LT TL VL NL : Nat) (l1 l2 : List Nat) (x : Nat) :
    runHdr HB LT TL VL NL (List.append l1 l2) x =
      runHdr HB LT TL VL NL l2 (runHdr HB LT TL VL NL l1 x) :=
  chunkLoop_append _ l1 l2 x

theorem runGom_append (HB GB OB : Nat → Nat) (I0 nH : Nat) (l1 l2 : List Nat) (x : Nat) :
    runGom HB GB OB I0 nH (List.append l1 l2) x =
      runGom HB GB OB I0 nH l2 (runGom HB GB OB I0 nH l1 x) :=
  chunkLoop_append _ l1 l2 x

theorem runSorted_append (get : Nat → Nat) (qb m : Nat) (l1 l2 : List Nat) (x : Nat) :
    runSorted get qb m (List.append l1 l2) x = runSorted get qb m l2 (runSorted get qb m l1 x) :=
  chunkLoop_append _ l1 l2 x

theorem runT_append (TB OB RR : Nat → Nat) (LT TL VL NL NR nT I0 : Nat) (l1 l2 : List Nat)
    (x : Nat) :
    runT TB OB RR LT TL VL NL NR nT I0 (List.append l1 l2) x =
      runT TB OB RR LT TL VL NL NR nT I0 l2 (runT TB OB RR LT TL VL NL NR nT I0 l1 x) :=
  chunkLoop_append _ l1 l2 x

theorem runCover_append (FB OB : Nat → Nat) (sh wd NF NO AL : Nat) (l1 l2 : List Nat) (x : Nat) :
    runCover FB OB sh wd NF NO AL (List.append l1 l2) x =
      runCover FB OB sh wd NF NO AL l2 (runCover FB OB sh wd NF NO AL l1 x) :=
  chunkLoop_append _ l1 l2 x

theorem runStab_append (FB EB : Nat → Nat) (sh wd NF D SG : Nat) (l1 l2 : List Nat) (x : Nat) :
    runStab FB EB sh wd NF D SG (List.append l1 l2) x =
      runStab FB EB sh wd NF D SG l2 (runStab FB EB sh wd NF D SG l1 x) :=
  chunkLoop_append _ l1 l2 x

theorem stabOne_intro {FB : Nat → Nat} {sh wd NF MD D : Nat} {EB : Nat → Nat}
    {SG mD : Nat} {C1 : List Nat} {X0 X1 : Nat} {C2 : List Nat} {Y0 Y1 : Nat}
    (h1 : Nat.beq mD (bits MD (Nat.mul (nat_lit 20) D) (nat_lit 20)) = true)
    (h2 : stabStart EB = true) (h3 : Nat.beq X0 (nat_lit 2) = true)
    (h4 : Nat.beq (runStab FB EB sh wd NF D SG C1 X0) X1 = true)
    (h5 : Nat.beq X1 (Nat.succ mD) = true) (h6 : Nat.beq Y0 (nat_lit 1) = true)
    (h7 : Nat.beq (runSorted (mat EB) (nat_lit 19) mD C2 Y0) Y1 = true)
    (h8 : Nat.beq (sortedCount Y1) mD = true) :
    stabOne FB sh wd NF MD (D, EB, SG, mD, C1, X0, X1, C2, Y0, Y1) = true :=
  andB_intro' h1 (andB_intro' h2 (andB_intro' h3 (andB_intro' h4 (andB_intro' h5 (andB_intro' h6
    (andB_intro' h7 h8))))))

theorem stabAll_cons {FB : Nat → Nat} {sh wd NF MD : Nat}
    {s : Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat))))))))}
    {L : List (Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat)))))))))}
    (h : stabOne FB sh wd NF MD s = true) (h' : stabAll FB sh wd NF MD L = true) :
    stabAll FB sh wd NF MD (s :: L) = true :=
  andB_intro' h h'

theorem stabAll_nil (FB : Nat → Nat) (sh wd NF MD : Nat) : stabAll FB sh wd NF MD [] = true := rfl

theorem dceOk_intro {FB HB GB TB WD OB RR : Nat → Nat}
    {sh wd LT LI TL VL NL ND NO nH nT nW NR NF I0 W Wi USQ UH WH AL MD NORD SUM qO qT : Nat}
    {Cs : List Nat} {S0 S1 : Nat} {Hs : List Nat} {H0 H1 : Nat} {Gs : List Nat} {G0 G1 : Nat}
    {Os : List Nat} {O0 O1 : Nat} {TSs : List Nat} {T0 T1 : Nat} {Ts : List Nat} {P0 P1 : Nat}
    {Vs : List Nat} {V0 V1 : Nat}
    {stabs : List (Nat × ((Nat → Nat) × (Nat × (Nat × (List Nat × (Nat × (Nat × (List Nat × (Nat × Nat)))))))))}
    (h0 : constsOK7 = true)
    (h1 : lettersOK LT LI TL VL NL = true) (h2 : relsOK RR LT TL VL NL NR = true)
    (h3 : relsNorm RR NR = true) (h4 : wordsOK WD RR LI NL NR WH nW = true)
    (h5 : usqOK RR LT LI TL VL NL NR USQ W Wi UH = true) (h6 : Nat.blt ND (nat_lit 255) = true)
    (h7 : Nat.blt I0 NO = true) (h8 : Nat.beq (Nat.mul nT NO) NORD = true)
    (h9 : sumOK AL MD ND NORD SUM = true) (h10 : Nat.blt NF (nat_lit 4294967296) = true)
    (h11 : Nat.beq H0 (nat_lit 1) = true) (h12 : Nat.beq (runHdr HB LT TL VL NL Hs H0) H1 = true)
    (h13 : Nat.beq H1 (Nat.succ nH) = true) (h14 : Nat.beq G0 (nat_lit 1) = true)
    (h15 : Nat.beq (runGom HB GB OB I0 nH Gs G0) G1 = true) (h16 : Nat.beq G1 (Nat.succ NO) = true)
    (h17 : Nat.beq O0 (nat_lit 1) = true) (h18 : Nat.beq (runSorted (pt OB) qO NO Os O0) O1 = true)
    (h19 : Nat.beq (sortedCount O1) NO = true) (h20 : Nat.beq T0 (nat_lit 1) = true)
    (h21 : Nat.beq (runSorted (tS TB) qT nT TSs T0) T1 = true)
    (h22 : Nat.beq (sortedCount T1) nT = true) (h23 : Nat.beq P0 (nat_lit 1) = true)
    (h24 : Nat.beq (runT TB OB RR LT TL VL NL NR nT I0 Ts P0) P1 = true)
    (h25 : Nat.beq P1 (Nat.succ nT) = true)
    (h26 : Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)) = true)
    (h27 : Nat.beq (runFacts FB HB GB TB WD sh wd LT TL VL NL ND NO nH nT nW W Wi Cs S0) S1 = true)
    (h28 : Nat.blt (nat_lit 0) S1 = true) (h29 : Nat.beq (sI S1) NF = true)
    (h30 : Nat.beq V0 (nat_lit 1) = true)
    (h31 : Nat.beq (runCover FB OB sh wd NF NO AL Vs V0) V1 = true)
    (h32 : Nat.beq V1 (Nat.add (nat_lit 1) (Nat.shiftLeft ND (nat_lit 20))) = true)
    (h33 : stabAll FB sh wd NF MD stabs = true) (h34 : stabCover MD ND AL stabs = true) :
    dceOk FB HB GB TB WD OB RR sh wd LT LI TL VL NL ND NO nH nT nW NR NF I0 W Wi USQ UH WH AL MD
      NORD SUM qO qT Cs S0 S1 Hs H0 H1 Gs G0 G1 Os O0 O1 TSs T0 T1 Ts P0 P1 Vs V0 V1 stabs = true :=
  andB_intro' h0 (andB_intro' h1 (andB_intro' h2 (andB_intro' h3 (andB_intro' h4 (andB_intro' h5
  (andB_intro' h6 (andB_intro' h7 (andB_intro' h8 (andB_intro' h9 (andB_intro' h10 (andB_intro' h11
  (andB_intro' h12 (andB_intro' h13 (andB_intro' h14 (andB_intro' h15 (andB_intro' h16
  (andB_intro' h17 (andB_intro' h18 (andB_intro' h19 (andB_intro' h20 (andB_intro' h21
  (andB_intro' h22 (andB_intro' h23 (andB_intro' h24 (andB_intro' h25 (andB_intro' h26
  (andB_intro' h27 (andB_intro' h28 (andB_intro' h29 (andB_intro' h30 (andB_intro' h31
  (andB_intro' h32 (andB_intro' h33 h34)))))))))))))))))))))))))))))))))

end CFSG.Certificates.DS5

open CFSG.Certificates.LCE.Assemble CFSG.Certificates.DSP.Assemble in
elab "#ds5_ok " nm:ident ns:ident xs:ident fa:ident hd:ident go:ident os:ident ts:ident tt:ident
    cv:ident "[" ds:num,* "]" : command => do
  let N := ns.getId
  let X := xs.getId
  liftTermElabM do
    let sl := fun (i : Ident) => do sliceArgs (← getConstInfo i.getId).type
    let (_, aF, Cs, S0, S1) ← sl fa
    let (_, _, Hs, H0, H1) ← sl hd
    let (_, aG, Gs, G0, G1) ← sl go
    let (_, aO, Os, O0, O1) ← sl os
    let (_, aTS, TSs, T0, T1) ← sl ts
    let (_, aT, Ts, P0, P1) ← sl tt
    let (_, aV, Vs, V0, V1) ← sl cv
    let aLet ← eqArgs (N ++ `xLet)
    let aWords ← eqArgs (N ++ `xWords)
    let aUsq ← eqArgs (N ++ `xUsq)
    let aSum ← eqArgs (N ++ `xSum)
    let FB := aF[0]!
    let HB := aF[1]!
    let GB := aF[2]!
    let TB := aF[3]!
    let WD := aF[4]!
    let sh := aF[5]!
    let wd := aF[6]!
    let LT := aF[7]!
    let TL := aF[8]!
    let VL := aF[9]!
    let NL := aF[10]!
    let ND := aF[11]!
    let NO := aF[12]!
    let nH := aF[13]!
    let nT := aF[14]!
    let nW := aF[15]!
    let W := aF[16]!
    let Wi := aF[17]!
    let OB := aG[2]!
    let I0 := aG[3]!
    let RR := aT[2]!
    let NR := aT[7]!
    let NF := aV[4]!
    let AL := aV[6]!
    let qO := aO[1]!
    let qT := aTS[1]!
    let LI := aLet[1]!
    let WH := aWords[5]!
    let USQ := aUsq[7]!
    let UH := aUsq[10]!
    let MD := aSum[1]!
    let NORD := aSum[3]!
    let SUM := aSum[4]!
    let mut recs : Array (Expr × Expr) := #[]
    for d in ds.getElems do
      let D := d.getNat
      let sjN := X ++ Name.mkSimple s!"sj{D}"
      let ejN := X ++ Name.mkSimple s!"ej{D}"
      let (_, aS, C1, X0, X1) ← sliceArgs (← getConstInfo sjN).type
      let (_, aE, C2, Y0, Y1) ← sliceArgs (← getConstInfo ejN).type
      let EB := aS[1]!
      let Dl := aS[5]!
      let SG := aS[6]!
      let mD := aE[2]!
      let r := mkRec #[Dl, EB, SG, mD, C1, X0, X1, C2, Y0, Y1]
      let pf := mkAppN (mkConst ``CFSG.Certificates.DS5.stabOne_intro)
        #[FB, sh, wd, NF, MD, Dl, EB, SG, mD, C1, X0, X1, C2, Y0, Y1, reflBoolTrue,
          mkConst (N ++ Name.mkSimple s!"xE{D}"), reflBoolTrue,
          mkConst sjN, reflBoolTrue, reflBoolTrue,
          mkConst ejN, reflBoolTrue]
      recs := recs.push (r, pf)
    let elT := (recTypes)[0]!
    let nilL := mkApp (mkConst ``List.nil [Level.zero]) elT
    let (stabs, stabPf) := recs.foldr (fun (r, pf) (L, pL) =>
      (mkApp3 (mkConst ``List.cons [Level.zero]) elT r L,
        mkAppN (mkConst ``CFSG.Certificates.DS5.stabAll_cons) #[FB, sh, wd, NF, MD, r, L, pf, pL]))
      (nilL, mkAppN (mkConst ``CFSG.Certificates.DS5.stabAll_nil) #[FB, sh, wd, NF, MD])
    let args := #[FB, HB, GB, TB, WD, OB, RR, sh, wd, LT, LI, TL, VL, NL, ND, NO, nH, nT, nW, NR, NF,
      I0, W, Wi, USQ, UH, WH, AL, MD, NORD, SUM, qO, qT, Cs, S0, S1, Hs, H0, H1, Gs, G0, G1, Os, O0,
      O1, TSs, T0, T1, Ts, P0, P1, Vs, V0, V1, stabs]
    let c := fun (s : Name) => mkConst (N ++ s)
    let relsPf := mkAppN (mkConst ``CFSG.Certificates.DS5.andB_right')
      #[(← eqArgs (N ++ `xRel))[0]!, (← eqArgs (N ++ `xRel))[1]!, c `xRel]
    let pf := mkAppN (mkConst ``CFSG.Certificates.DS5.dceOk_intro) (args ++
      #[c `xConsts, c `xLet, relsPf, reflBoolTrue, c `xWords, c `xUsq, c `xND, c `xI0, c `xT5,
        c `xSum, reflBoolTrue, reflBoolTrue, mkConst hd.getId, reflBoolTrue, reflBoolTrue,
        mkConst go.getId, reflBoolTrue, reflBoolTrue, mkConst os.getId, reflBoolTrue,
        reflBoolTrue, mkConst ts.getId, reflBoolTrue, reflBoolTrue, mkConst tt.getId,
        reflBoolTrue, reflBoolTrue, mkConst fa.getId, reflBoolTrue, reflBoolTrue, reflBoolTrue,
        mkConst cv.getId, reflBoolTrue, stabPf, reflBoolTrue])
    let type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
      (mkAppN (mkConst ``CFSG.Certificates.DS5.dceOk) args) (mkConst ``Bool.true)
    withOptions (Elab.async.set · false) <|
      CFSG.KC.addThmDecl <| { name := nm.getId, levelParams := [], type, value := pf }

end

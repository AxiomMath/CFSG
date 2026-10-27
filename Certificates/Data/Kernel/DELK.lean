module

public import Certificates.Data.DepED4Low
public import Certificates.Data.Kernel.TWLK6

public section

namespace Certificates.DELK

open Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallLow
  Certificates.DepED4Low
open Certificates.TWLK (kAll2 kVKey kIncr)

set_option compiler.extract_closed false

abbrev KSub := List (List Nat) × List (List Nat) × List (Nat × Nat) × List (List Nat) × List Nat

@[expose] def kTupApply (A : List (List Nat)) (t : List (List Nat)) : List (List Nat) :=
  t.map (ggTWLMatApply 3 6 A)

@[expose] def kOrbReplay (G : List (List (List Nat))) (B : List (List Nat))
    (par : List (Nat × Nat)) : List (List (List Nat)) :=
  par.foldl (fun V e => V ++ [kTupApply (G.getD e.2 []) (V.getD e.1 [])]) [B]

@[expose] def kOrbOK (G : List (List (List Nat))) (B : List (List Nat)) (par : List (Nat × Nat))
    (cl : List (List Nat)) (ord : List Nat) : Bool :=
  let V := kOrbReplay G B par
  B.all (fun v => decide (v.length = 6)) &&
    (List.range par.length).all (fun i => decide ((par.getD i (0, 0)).1 < i + 1) &&
      decide ((par.getD i (0, 0)).2 < G.length)) &&
    kAll2 (fun t row => kAll2 (fun g c => kAll2 (ggTWLVecEq 3) (V.getD c []) (kTupApply g t)) G row)
      V cl &&
    decide (ord.length = V.length) && ord.all (fun i => decide (i < V.length)) &&
    kIncr (ord.map fun i => kVKey 3 (V.getD i []))

@[expose] def kCen (Om : List (List (List Nat))) (a : List (List Nat)) : Bool :=
  !ggTWLMatEq 3 a (ggTWLMatOne 6) &&
    Om.all fun t => ggTWLMatEq 3 (ggTWLMatMul 3 6 a t) (ggTWLMatMul 3 6 t a)

@[expose] def kSubOK (Om : List (List (List Nat))) (s : KSub) : Bool :=
  s.1.all (fun u => u.all fun j => decide (j < Om.length)) &&
    kOrbOK (s.1.map (ggTWLWordMat 3 6 Om)) s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2

@[expose] def kPZBase (P : List GGDepANPair) (subs : List KSub) (cen : List Nat) : Bool :=
  let Om := P.map (ggTWLMatOfPair 3 6)
  let K := subs.foldl (fun k s => Nat.lcm k (s.2.2.1.length + 1)) 1
  let cenOK := cen.all (fun j => decide (j < Om.length)) &&
    kCen Om (ggTWLWordMat 3 6 Om cen)
  subs.all (kSubOK Om) && cenOK && ggTWLPZArith 7 K cenOK

@[expose] def kPZConj (P Q : List GGDepANPair) (m mi : List (List Nat)) : Bool :=
  decide (m.length = 6) && decide (mi.length = 6) &&
    ggTWLMatEq 3 (ggTWLMatMul 3 6 m mi) (ggTWLMatOne 6) &&
    ggTWLMatEq 3 (ggTWLMatMul 3 6 mi m) (ggTWLMatOne 6) &&
    decide (P.length = Q.length) &&
    kAll2 (fun a b => ggTWLMatEq 3 (ggTWLMatMul 3 6 (ggTWLMatMul 3 6 m (ggTWLMatOfPair 3 6 a)) mi)
      (ggTWLMatOfPair 3 6 b)) P Q

abbrev KBase := Nat × List KSub × List Nat

abbrev KConj := Nat × Nat × List (List Nat) × List (List Nat)

@[expose] def kBaseAt (Ps : List (List GGDepANPair)) (S : List KBase) (i : Nat) : Bool :=
  match S[i]? with
  | some e => decide (e.1 < Ps.length) && kPZBase (Ps.getD e.1 []) e.2.1 e.2.2
  | none => false

@[expose] def kConjAt (Ps : List (List GGDepANPair)) (S : List KBase) (C : List KConj) (i : Nat) :
    Bool :=
  match C[i]? with
  | some e => decide (e.1 < Ps.length) && (S.map (·.1)).contains e.2.1 &&
      kPZConj (Ps.getD e.2.1 []) (Ps.getD e.1 []) e.2.2.1 e.2.2.2
  | none => false

@[expose] def kGroupsCover (Ps : List (List GGDepANPair)) (S : List KBase) (C : List KConj) :
    Bool :=
  (List.range Ps.length).all fun g => (S.map (·.1)).contains g || (C.map (·.1)).contains g

abbrev KPZ := (Nat × List (Nat × List Nat) × List (Nat × List Nat × List Nat)) × Nat

@[expose] def kZ0 : KPZ := ((0, [], []), 0)

@[expose] def kPairsEq (P Q : List GGDepANPair) : Bool :=
  kAll2 (fun a b => ggTWLVecEq 3 a.1 b.1 && ggTWLVecEq 3 a.2 b.2) P Q

@[expose] def kPZRef (Ps : List (List GGDepANPair)) (news : List GGDepANPair) (y : List Nat)
    (e : KPZ) : Bool :=
  let c0 := e.1.1
  let fixs := e.1.2.1
  let orbs := e.1.2.2
  let G := 6 + news.length
  let z := ggTWNAdd 3 ggDepELNX (ggDepANSmul 3 c0 y)
  let fixP : List GGDepANPair := fixs.map fun e => ggDepELNWord news (ggDepELNGen news e.1) e.2
  let orbP : List GGDepANPair := orbs.map fun e =>
    e.2.2.foldr (fun k acc => ggDepANConj 3 acc (fixP.getD k ([], [])))
      (ggDepELNWord news (ggDepELNGen news e.1) e.2.1)
  decide (0 < c0) && decide (c0 < 3) &&
    fixs.all (fun e => decide (e.1 < G) && e.2.all fun g => decide (g < G)) &&
    orbs.all (fun e => ggDepELNInJ e.1 && e.2.1.all ggDepELNInJ &&
      e.2.2.all fun k => decide (k < fixP.length)) &&
    fixP.all (fun s => ggDepANDot 3 s.2 z == 0) &&
    decide (e.2 < Ps.length) && kPairsEq orbP (Ps.getD e.2 [])

abbrev KHK := (Nat × List Nat × Nat × List Nat) × List (List Nat)

@[expose] def kH0 : KHK := ((0, [], 0, []), [])

@[expose] def kHKTest (news : List GGDepANPair) (y : List Nat) (h : KHK) : Bool :=
  let og := ggDepELNOGens news
  let G := 6 + news.length
  let w : GGTWLHK := ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2⟩
  let R := h.2
  let s := ggDepELNWord news (ggDepELNGen news w.g) w.w
  let v := w.ow.foldr (fun k acc => ggTWNRefl 3 (og.getD k ([], [])) acc)
    (og.getD w.oc ([], [])).1
  let sv := ggTWNRefl 3 s v
  decide (w.g < G) && w.w.all (fun g => decide (g < G)) && decide (w.oc < og.length) &&
    w.ow.all (fun k => decide (k < og.length)) &&
    ggTWLStable 3 og (og.map (·.1)) R &&
    ggDepANDot 3 s.2 y % 3 == 0 &&
    R.all fun u => !ggTWLParMod 3 y u sv

@[expose] def kRT (H : List KHK) (Z : List KPZ) (Ps : List (List GGDepANPair))
    (news : List GGDepANPair) (r : Nat × Nat) : Bool :=
  if r.1 = 1 then kHKTest news (ggDepELY0 news) (H.getD r.2 kH0)
  else if r.1 = 2 then kPZRef Ps news (ggDepELY0 news) (Z.getD r.2 kZ0)
  else false

abbrev KWit := Nat × List Nat × Nat × List Nat

@[expose] def kWit (w : KWit) : GGDepANWit := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2⟩

@[expose] def kCases1 (rt : List GGDepANPair → Nat × Nat → Bool) (c0 : Nat) (wits : List KWit)
    (exc : List ((List Nat × List Nat) × (Nat × Nat))) : Bool :=
  let has := ggDepELSolH fun c => if c = c0 then 2 else 0
  let aas := ggDepELSolA fun c => if c = c0 then 2 else 0
  has.all fun ha => aas.all fun aa =>
    if ggDepANDot 3 aa ha == 2 && ggDepANDot 3 aa ggDepELNX != 0 then
      match exc.find? (fun e => ggTWLVecEq 3 e.1.1 ha && ggTWLVecEq 3 e.1.2 aa) with
      | some e => rt [(ha, aa)] e.2
      | none => wits.any fun w => ggDepELTvTest [(ha, aa)] (kWit w)
    else true

@[expose] def kCases2 (rt : List GGDepANPair → Nat × Nat → Bool) (c c' : Nat) (wits : List KWit)
    (exc : List ((List Nat × List Nat × List Nat × List Nat) × (Nat × Nat))) : Bool :=
  let h1s := ggDepELSolH fun d => if d = c then 2 else 0
  let a1s := ggDepELSolA fun d => if d = c then 2 else 0
  let h2s := ggDepELSolH fun d => if d = c' then 2 else 0
  let a2s := ggDepELSolA fun d => if d = c' then 2 else 0
  h1s.all fun h1 => a1s.all fun a1 =>
    if ggDepANDot 3 a1 h1 == 2 then
      h2s.all fun h2 =>
        if ggDepANDot 3 a1 h2 == 0 then
          a2s.all fun a2 =>
            if ggDepANDot 3 a2 h2 == 2 && ggDepANDot 3 a2 h1 == 0 &&
                (ggDepANDot 3 a1 ggDepELNX != 0 || ggDepANDot 3 a2 ggDepELNX != 0) &&
                (ggDepANDot 3 a1 ggDepELNX * ggDepANDot 3 a2 ggDepELNZ) % 3 ==
                  (ggDepANDot 3 a1 ggDepELNZ * ggDepANDot 3 a2 ggDepELNX) % 3 then
              match exc.find? (fun e => ggTWLVecEq 3 e.1.1 h1 && ggTWLVecEq 3 e.1.2.1 a1 &&
                  ggTWLVecEq 3 e.1.2.2.1 h2 && ggTWLVecEq 3 e.1.2.2.2 a2) with
              | some e => rt [(h1, a1), (h2, a2)] e.2
              | none => wits.any fun w => ggDepELTvTest [(h1, a1), (h2, a2)] (kWit w)
            else true
        else true
    else true

abbrev KPat1 := Nat × List KWit × List ((List Nat × List Nat) × (Nat × Nat))

abbrev KPat2 :=
  (Nat × Nat) × List KWit × List ((List Nat × List Nat × List Nat × List Nat) × (Nat × Nat))

@[expose] def kPat1At (H : List KHK) (Z : List KPZ) (Ps : List (List GGDepANPair))
    (O : List KPat1) (i : Nat) : Bool :=
  match O[i]? with
  | some e => e.2.1.all (fun w => ggDepELTvValid 7 (kWit w)) &&
      kCases1 (kRT H Z Ps) e.1 e.2.1 e.2.2
  | none => false

@[expose] def kPat2At (H : List KHK) (Z : List KPZ) (Ps : List (List GGDepANPair))
    (T : List KPat2) (i : Nat) : Bool :=
  match T[i]? with
  | some e => e.2.1.all (fun w => ggDepELTvValid 8 (kWit w)) &&
      kCases2 (kRT H Z Ps) e.1.1 e.1.2 e.2.1 e.2.2
  | none => false

@[expose] def kCover (O : List KPat1) (T : List KPat2) : Bool :=
  ggDepELNLeaves.all (fun c => (O.map (·.1)).contains c) &&
    ggDepELNLeaves.all fun c => ggDepELNLeaves.all fun c' =>
      c == c' || (T.map (·.1)).contains (c, c')

end Certificates.DELK

end

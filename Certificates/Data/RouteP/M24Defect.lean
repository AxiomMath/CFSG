module

public import CFSG.Quasithin.Background.HMathieuMask
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace Certificates.RouteP.M24Defect

open CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] def idA : Array ℕ := Array.ofFn fun i : Fin 24 => (i : ℕ)

@[expose] def compA (a b : Array ℕ) : Array ℕ := Array.ofFn fun i : Fin 24 => a[b[(i : ℕ)]!]!

@[expose] def aArr : Array ℕ :=
  #[3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]

@[expose] def aInv : Array ℕ :=
  #[3, 4, 20, 0, 1, 13, 18, 11, 19, 16, 23, 7, 14, 5, 12, 22, 9, 21, 6, 8, 2, 17, 15, 10]

@[expose] def bArr : Array ℕ :=
  #[18, 14, 13, 0, 4, 5, 2, 17, 8, 1, 10, 19, 20, 6, 9, 12, 16, 22, 3, 23, 15, 21, 7, 11]

@[expose] def bInv : Array ℕ :=
  #[3, 9, 6, 18, 4, 5, 13, 22, 8, 14, 10, 23, 15, 2, 1, 20, 16, 7, 0, 11, 12, 21, 17, 19]

@[expose] def letArr (i : ℕ) (s : Bool) : Array ℕ :=
  if i = 0 then (if s then aArr else aInv) else (if s then bArr else bInv)

@[expose] def wordA : List (ℕ × Bool) → Array ℕ
  | [] => idA
  | l :: w => compA (letArr l.1 l.2) (wordA w)

@[expose] def wordAInv : List (ℕ × Bool) → Array ℕ
  | [] => idA
  | l :: w => compA (wordAInv w) (letArr l.1 !l.2)

structure HA where
  fwd : Array ℕ
  bwd : Array ℕ

@[expose] def HA.one : HA := ⟨idA, idA⟩

@[expose] def HA.step (st : HA) (i : ℕ) (s : Bool) : HA :=
  ⟨compA st.fwd (letArr i s), compA (letArr i !s) st.bwd⟩

@[expose] def edgeStates : List (ℕ × Bool) → HA → List (HA × ℕ)
  | [], _ => []
  | (i, s) :: w, st => ((if s then st else st.step i s), i) :: edgeStates w (st.step i s)

@[expose] def relWords : List (List (ℕ × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true)],
    (List.replicate 23 [(0, true), (1, true)]).flatten,
    (List.replicate 12 [(0, false), (1, false), (0, true), (1, true)]).flatten,
    (List.replicate 5 [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true),
      (0, true), (1, true)]).flatten,
    [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true),
      (0, true), (1, false), (0, true), (1, false)],
    (List.replicate 4 [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
      (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true),
      (1, false)]).flatten]

@[expose] def xorMasks : List ℕ → ℕ
  | [] => 0
  | m :: l => m ^^^ xorMasks l

@[expose] def dualAct : List ℕ → ℕ → ℕ
  | [], _ => 0
  | c :: cs, m => popc 11 (m &&& c) % 2 + 2 * dualAct cs m

@[expose] def matA (a : Array ℕ) : List ℕ := matOf 11 (act11 a)

@[expose] def tword (tab : Array (List (ℕ × Bool))) (q : ℕ) : List (ℕ × Bool) := tab[q]!

@[expose] def startHA (tab : Array (List (ℕ × Bool))) (p : ℕ) : HA :=
  ⟨wordA (tword tab p), wordAInv (tword tab p)⟩

@[expose] def ptIdx (st : HA) : ℕ := 24 * st.bwd[0]! + st.bwd[1]!

@[expose] def kArr (tab : Array (List (ℕ × Bool))) (st : HA) : Array ℕ :=
  compA st.fwd (wordAInv (tword tab (ptIdx st)))

@[expose] def keyOf (st : HA) (x : ℕ) : ℕ := 2 * ptIdx st + x

@[expose] def contribs (tab : Array (List (ℕ × Bool))) (p i m : ℕ) : List (ℕ × ℕ) :=
  (edgeStates (relWords[i]!) (startHA tab p)).map fun e =>
    (keyOf e.1 e.2, dualAct (matA (kArr tab e.1)) m)

@[expose] def fpart (tab : Array (List (ℕ × Bool))) (p m : ℕ) : ℕ :=
  dualAct (matA (wordA (tword tab p))) m

@[expose] def comboContribs (tab : Array (List (ℕ × Bool))) (ents : List (ℕ × ℕ × ℕ)) :
    List (ℕ × ℕ) :=
  ents.flatMap fun e => contribs tab e.1 e.2.1 e.2.2

@[expose] def bucket (L : List (ℕ × ℕ)) (κ : ℕ) : ℕ :=
  xorMasks ((L.filter fun x => x.1 == κ).map Prod.snd)

@[expose] def bucketsZero (L : List (ℕ × ℕ)) : Bool :=
  L.all (fun x => x.1 < 1152) && (List.range 1152).all fun κ => bucket L κ == 0

@[expose] def comboF (tab : Array (List (ℕ × Bool))) (ents : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ :=
  xorMasks ((ents.filter fun e => e.2.1 == i).map fun e => fpart tab e.1 e.2.2)

@[expose] def comboFs (tab : Array (List (ℕ × Bool))) (ents : List (ℕ × ℕ × ℕ)) : List ℕ :=
  (List.range 7).map (comboF tab ents)

@[expose] def entriesOK (ents : List (ℕ × ℕ × ℕ)) : Bool :=
  ents.all fun e => e.1 / 24 < 24 && e.1 % 24 < 24 && e.1 / 24 != e.1 % 24 && e.2.1 < 7 &&
    e.2.2 < 2048

@[expose] def treeOK (tab : Array (List (ℕ × Bool))) : Bool :=
  tab.size == 576 && (List.range 24).all fun u => (List.range 24).all fun v =>
    u == v || ((wordAInv (tword tab (24 * u + v)))[0]! == u &&
      (wordAInv (tword tab (24 * u + v)))[1]! == v)

@[expose] def treeLetters (tab : Array (List (ℕ × Bool))) : Bool :=
  tab.all fun w => w.all fun l => l.1 < 2 && l.2

@[expose] def fbit (f : List ℕ) (κ : ℕ) : Bool := (f[κ / 11]!).testBit (κ % 11)

@[expose] def unitMask (κ i : ℕ) : ℕ := if κ / 11 = i then 2 ^ (κ % 11) else 0

@[expose] def lamApply (v : ℕ × ℕ) (i : ℕ) : ℕ :=
  xorMasks ((edgeStates (relWords[i]!) HA.one).map fun e =>
    actM (matA e.1.fwd) (if e.2 = 0 then v.1 else v.2))

@[expose] def bezoutOK (Fs : List (List ℕ)) (S : List (ℕ × ℕ)) (T : List (List ℕ)) : Bool :=
  Fs.length == 67 && S.length == 77 && T.length == 67 &&
    S.all (fun v => v.1 < 2048 && v.2 < 2048) && T.all (fun t => t.length == 7) &&
    (List.range 77).all fun κ => (List.range 7).all fun i =>
      (lamApply S[κ]! i ^^^
        xorMasks (((List.range 67).filter fun r => fbit Fs[r]! κ).map fun r => (T[r]!)[i]!)) ==
        unitMask κ i

@[expose] def treeText : String := include_str "M24DefectTree.txt"

@[expose] def comboText : String := include_str "M24DefectCombos.txt"

@[expose] def bezoutText : String := include_str "M24DefectBezout.txt"

@[expose] def parseNats (s : String) : List ℕ :=
  (s.splitOn " ").filterMap fun t => if t = "" then none else some t.toNat!

@[expose] def parseWord (s : String) : List (ℕ × Bool) :=
  s.toList.filterMap fun ch => if ch = '0' then some (0, true) else
    if ch = '1' then some (1, true) else none

@[expose] def treeTab (_ : Unit := ()) : Array (List (ℕ × Bool)) :=
  (treeText.splitOn "\n").foldl (fun a line =>
    match line.splitOn " " with
    | [u, v, bits] => a.set! (24 * u.toNat! + v.toNat!) (parseWord bits)
    | _ => a) (Array.replicate 576 [])

@[expose] def comboData (_ : Unit := ()) : List (List (ℕ × ℕ × ℕ)) :=
  ((comboText.splitOn "C\n").drop 1).map fun blk =>
    (blk.splitOn "\n").filterMap fun line =>
      match parseNats line with
      | [p, i, m] => some (p, i, m)
      | _ => none

@[expose] def sData (_ : Unit := ()) : List (ℕ × ℕ) :=
  let ls := (bezoutText.splitOn "\n").filter (· != "")
  ((ls.drop 1).takeWhile (· != "T")).filterMap fun line =>
    match parseNats line with
    | [a, b] => some (a, b)
    | _ => none

@[expose] def tData (_ : Unit := ()) : List (List ℕ) :=
  let ls := (bezoutText.splitOn "\n").filter (· != "")
  ((ls.dropWhile (· != "T")).drop 1).map parseNats

@[expose] def lettersOK : Bool :=
  compA aArr aInv == idA && compA aInv aArr == idA && compA bArr bInv == idA &&
    compA bInv bArr == idA

@[expose] def relsOK : Bool := relWords.all fun w => wordA w == idA

@[expose] def checkAll (_ : Unit := ()) : Bool :=
  let tab := treeTab ()
  let cs := comboData ()
  let Fs := cs.map (comboFs tab)
  lettersOK && relsOK && treeOK tab && treeLetters tab && cs.length == 67 &&
    cs.all (fun ents => entriesOK ents && bucketsZero (comboContribs tab ents)) &&
    bezoutOK Fs (sData ()) (tData ())

end Certificates.RouteP.M24Defect

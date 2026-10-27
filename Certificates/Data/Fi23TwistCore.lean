module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23ThreeInputs
public import Certificates.Data.CFSGNative.Fi23.Classes
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23ThreeInputs
public meta import Certificates.Data.CFSGNative.Fi23.Classes
public meta import Certificates.Data.CFSGNative.Fi23.Centralizer

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23TwistNative

open CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native
  CFSG.HardMathSupport.Foote.E27 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

set_option compiler.extract_closed false

@[expose] def twEnum (G : Array Table) (n : Nat) : QEnum := Id.run do
  let m := G.size
  let mut par : Array (Nat × Nat) := #[(0, 0)]
  let mut img : Array Nat := #[0, 1, 2, 3, 4, 5]
  let mut L : Array (Array Nat) := Array.replicate m #[]
  let mut H : Std.HashMap (UInt64 × UInt64) Nat := Std.HashMap.emptyWithCapacity (2 * n)
  H := H.insert (qKeyAt img 0) 0
  for i in [0:n] do
    if i < par.size then
      for j in [0:m] do
        let nb := qStepImg G[j]! img (6 * i)
        let k := qKeyAt nb 0
        match H.get? k with
        | some idx => L := L.modify j (·.push idx)
        | none =>
          let idx := par.size
          H := H.insert k idx
          img := img ++ nb
          par := par.push (i, j)
          L := L.modify j (·.push idx)
  return { par, img, L, H }

@[expose] def baseImg (T : Table) : Array Nat := qStepImg T #[0, 1, 2, 3, 4, 5] 0

@[expose] def twFind (E : QEnum) (n : Nat) (img : Array Nat) : Bool :=
  match E.H.get? (qKeyAt img 0) with
  | some i => decide (i < n) && allIn 0 6 fun t => E.img[6 * i + t]! == img[t]!
  | none => false

@[expose] def twEnumOK (G : Array Table) (E : QEnum) (n : Nat) : Bool :=
  qTreeOK G E.par E.img n && qLeftOK G E.L E.img n && qInjOK E.H E.img n

@[expose] def twWordsOK (m : Nat) (W : Array (List Nat)) : Bool :=
  W.all fun w => w.all fun z => decide (z < m)

@[expose] def twInvIdx (P : Array (Nat × Nat)) (L : Array (Array Nat)) (n : Nat) : Array Nat :=
  (Array.range n).map fun w => ((List.range n).find? fun v => tabMul P L w v == 0).getD 0

@[expose] def twInvOK (P : Array (Nat × Nat)) (L : Array (Array Nat)) (n : Nat)
    (inv : Array Nat) : Bool :=
  allIn 0 n fun w => decide (inv[w]! < n) && tabMul P L w inv[w]! == 0

@[expose] def twRepsOK (P : Array (Nat × Nat)) (L : Array (Array Nat)) (n k : Nat)
    (R : Array (Array Nat)) : Bool :=
  R.all fun S => S.size == 3 ^ k && S.all (fun a => decide (a < n)) &&
    allIn 1 S.size (fun i => decide (S[i - 1]! < S[i]!)) &&
    S.all fun a => S.all fun b => S.contains (tabMul P L a b)

@[expose] def twStepOK (P : Array (Nat × Nat)) (L : Array (Array Nat)) (n : Nat)
    (inv : Array Nat) (R S : Array (Array Nat)) (find : Nat → Nat → Nat × Nat) : Bool :=
  allIn 0 R.size fun j => allIn 0 n fun x =>
    R[j]!.contains x || tabMul P L x (tabMul P L x x) != 0 ||
      !(R[j]!.all fun a => tabMul P L a x == tabMul P L x a) ||
      (let f := find j x
       decide (f.1 < n) && decide (f.2 < S.size) &&
         (R[j]!.push x).all fun a => S[f.2]!.contains (tabMul P L (tabMul P L f.1 a) inv[f.1]!))

@[expose] def twClassOK (P : Array (Nat × Nat)) (L : Array (Array Nat)) (n : Nat)
    (inv : Array Nat) (reps : Array (Array (Array Nat)))
    (find : Nat → Nat → Nat → Nat × Nat) : Bool :=
  reps.size == 5 && reps[0]! == #[#[0]] && allIn 1 5 (fun k => twRepsOK P L n k reps[k]!) &&
    allIn 0 4 fun k => twStepOK P L n inv reps[k]! reps[k + 1]! (find k)

structure TwCent where
  hW : List Nat
  yIdx : Array Nat
  om : Nat
  cW : Array (List Nat)
  nC : Nat
  uW : Array (List Nat)
  e : Nat
  deriving Inhabited

@[expose] def conjImg (T V TI : Table) : Array Nat := qStepImg T (qStepImg V (baseImg TI) 0) 0

@[expose] def forcedImg (hT hI : Table) (P : Array (Nat × Nat)) (G : Array Table)
    (yIdx : Array Nat) (w : Nat) : Array Nat :=
  yIdx.map fun y => ap hT (qActPt P G y (ap hI w))

@[expose] def twCentOK (letters : Array Table) (trees : Array Tree) (qb : Array Nat)
    (P : Array (Nat × Nat)) (G : Array Table) (S : Array Nat) (c : TwCent) : Bool :=
  let hT := qLettersT letters c.hW
  let hI := invT 31671 hT
  let CG := c.cW.map (qLettersT letters)
  let UG := c.uW.map (qLettersT letters)
  let nU := 3 ^ c.e
  let EC := twEnum CG c.nC
  let EU := twEnum UG nU
  twWordsOK letters.size #[c.hW] && twWordsOK letters.size c.cW &&
    twWordsOK letters.size c.uW && invOK 31671 hT hI && twEnumOK CG EC c.nC &&
    twEnumOK UG EU nU && c.nC % nU == 0 && c.nC / nU % 3 != 0 &&
    UG.all (fun V => twFind EC c.nC (baseImg V)) &&
    CG.all (fun T =>
      let TI := invT 31671 T
      invOK 31671 T TI && UG.all fun V => twFind EU nU (conjImg T V TI)) &&
    c.yIdx.size == 6 && decide (c.om < 31671) &&
    allIn 0 6 (fun t => S.contains c.yIdx[t]! && ap hT (qActPt P G c.yIdx[t]! (ap hI c.om)) == t) &&
    allIn 0 31671 fun w =>
      let img := forcedImg hT hI P G c.yIdx w
      !(sift trees letters qb chainQ 0 img) || twFind EC c.nC img

@[expose] def twFixOK (img : Array Nat) (n : Nat) : Bool :=
  allIn 0 n fun i => img[6 * i]! == 0 && img[6 * i + 1]! == 1

@[expose] def twStabOK (D0 D1 : Table) (P : Array (Nat × Nat)) (G : Array Table) (n : Nat) :
    Bool :=
  allIn 0 31671 fun p => p == 0 || p == 1 || ap D0 p != p || ap D1 p != p ||
    decide ((List.range n).countP (fun i => qActPt P G i p == p) < 243)

@[expose] def twCommOK (X : Table) (G : Array Table) : Bool :=
  G.all fun T => allIn 0 31671 fun p => ap T (ap X p) == ap X (ap T p)

@[expose] def twFixSet (P : Array (Nat × Nat)) (G : Array Table) (S : Array Nat) : Array Nat :=
  (Array.range 31671).filter fun p => S.all fun i => qActPt P G i p == p

@[expose] def twPairOK (pt : Nat → Table) (X : Table) (F : Array Nat) : Bool :=
  F.all fun p => F.all fun q => p == q || (p == 0 && q == 1) || (p == 1 && q == 0) ||
    ap (pt p) q != q || !twCommOK X #[compT 31671 (pt p) (pt q)]

structure TwSyl where
  qW : Array (List Nat)
  reps : Array (Array (Array Nat))
  find : Nat → Nat → Nat → Nat × Nat
  cent : Array TwCent

@[expose] def twSylOK (letters : Array Table) (trees : Array Tree) (qb : Array Nat)
    (G : Array Table) (E : QEnum) (n : Nat) (D : TwSyl) : Bool :=
  let inv := twInvIdx E.par E.L n
  twWordsOK letters.size D.qW && twEnumOK G E n && twInvOK E.par E.L n inv &&
    twClassOK E.par E.L n inv D.reps D.find && D.cent.size == D.reps[4]!.size &&
    allIn 0 D.cent.size fun j => twCentOK letters trees qb E.par G D.reps[4]![j]! D.cent[j]!

@[expose] def twSylBOK (letters : Array Table) (pt : Nat → Table) (X : Table) (G : Array Table)
    (E : QEnum) (n : Nat) (D : TwSyl) : Bool :=
  let inv := twInvIdx E.par E.L n
  twWordsOK letters.size D.qW && twEnumOK G E n && twInvOK E.par E.L n inv &&
    twClassOK E.par E.L n inv D.reps D.find &&
    D.reps[4]!.all fun S => twPairOK pt X (twFixSet E.par G S)

@[expose] def fi23TwistCheckOf (O : WOrbit) (B C : TwSyl) : Bool :=
  let letters := chainLetters O
  let trees := chainTrees 31671 letters chainBase
  let qb := chainQb ()
  let D0 := dTab O
  let pt := treeActTab O D0 (genTables O (-2))
  let D1 := pt 1
  let XB := compT 31671 D0 D1
  let X := compT 31671 XB (pt 39)
  let GB := B.qW.map (qLettersT letters)
  let EB := twEnum GB 729
  let GC := C.qW.map (qLettersT letters)
  let EC := twEnum GC 243
  twSylBOK letters pt XB GB EB 729 B && twFixOK EB.img 729 && twStabOK D0 D1 EB.par GB 729 &&
    twSylOK letters trees qb GC EC 243 C && twCommOK X GC

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi23TwistNative

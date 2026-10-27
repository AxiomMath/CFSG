module

public import Certificates.Data.CFSGNative.Fischer.Xi22

public section

namespace CFSG.Fischer.Native

open CFSG.F4.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def perpTabWith (TT : Array Table) (_ : Unit) : Array Flags :=
  Array.ofFn (n := 693) fun x =>
    let T := TT[x.val]!
    Array.ofFn (n := 693) fun y => ap T y.val == y.val

@[noinline, expose] def perpPerpOKWith (TT : Array Table) (P : Array Flags) (pl : Array (Array Nat))
    (LT : Array (Array Nat)) : Bool :=
  let D := pl[0]!
  allIn 0 693 fun q => P[0]![q]! ||
    (let N := D.filter fun w => P[w]![q]!
     N.size == 45 &&
       N.any (fun a => N.any fun b => a != b && P[a]![b]! &&
         LT[a * 693 + b]!.any fun c => c != a && c != b && N.contains c) &&
       N.all (fun a => N.all fun b =>
         a == b || !P[a]![b]! || N.any fun w => P[w]![a]! != P[w]![b]!) &&
       allIn 0 693 fun q' => P[0]![q']! || !(D.all fun w => P[w]![q]! == P[w]![q']!) ||
         q' == q || q' == ap TT[0]! q)

@[noinline, expose] def polarLinesChecksWith (TT : Array Table) (P : Array Flags) (LT : Array (Array Nat)) : Bool :=
  let pl := perpLists P
  let L := lineList P LT
  allIn 0 693 (fun p => pl[p]!.size == 181) && linesOK P pl LT &&
    lineListOK P LT L (lineIdx L) && twinsOK P pl LT && (perpPerpOKWith TT) P pl LT

@[expose] def polarLinesCertificateWith (TT : Array Table) (_ : Unit) : Bool :=
  let P := (perpTabWith TT) ()
  (polarLinesChecksWith TT) P (lineTab P)

@[noinline, expose] def deltaTabOKWith (TT : Array Table) (P : Array Flags) (D : Table) : Bool :=
  let Di := invT 693 D
  invOK 693 D Di &&
    allIn 0 693 (fun a => ap D a < 693 &&
      (let pa := P[a]!; let pda := P[ap D a]!; allIn 0 693 fun b => pda[ap D b]! == pa[b]!)) &&
    allIn 0 693 (fun p => let T := TT[p]!; let T' := TT[ap D p]!;
      allIn 0 693 fun q => ap D (ap T q) == ap T' (ap D q)) &&
    rootFlags 2 == imgFlags Di (rootFlags 1) && rootFlags 3 == imgFlags Di (rootFlags 2) &&
    rootFlags 1 == imgFlags Di (rootFlags 3)

@[expose] def deltaCertificateWith (TT : Array Table) (_ : Unit) : Bool :=
  (deltaTabOKWith TT) ((perpTabWith TT) ()) (deltaTab ())

@[expose] def clStepWith (TT : Array Table) (F : Flags) : Flags :=
  let M := members F
  M.foldl (fun a u => let T := TT[u]!; M.foldl (fun a v => a.set! (ap T v) true) a) F

@[expose] def clIterWith (TT : Array Table) : Nat → Flags → Flags
  | 0, F => F
  | k + 1, F => (clIterWith TT) k ((clStepWith TT) F)

@[noinline, expose] def lamOfWith (TT : Array Table) (lns : Array (Array Nat)) : Array Flags :=
  Array.ofFn (n := 1024) fun j => (clIterWith TT) 3 (lamStart lns j.val)

@[expose] def lamTabWith (TT : Array Table) (_ : Unit) : Array Flags := (lamOfWith TT) ((lamSel ()).map (lineC 0))

@[expose] def gWordsWith (TT : Array Table) (_ : Unit) : Array (List Nat) := Id.run do
  let T := TT
  let mut w : Array (List Nat) := Array.replicate 693 []
  let mut seen : Array Bool := (Array.replicate 693 false).set! 0 true
  let mut queue : Array Nat := #[0]
  for h in [0:693] do
    if h < queue.size then
      let x := queue[h]!
      for k in [0:31] do
        let p := 23 * k
        let y := ap T[p]! x
        if !seen[y]! then
          seen := seen.set! y true
          w := w.set! y (p :: w[x]!)
          queue := queue.push y
    else break
  return w

@[expose] def tvWordTabWith (TT : Array Table) (w : List Nat) : Table :=
  w.foldr (fun p T => compT 693 TT[p]! T) (idT 693)

@[noinline, expose] def wordInvsWith (TT : Array Table) (W : Array (List Nat)) : Array Table :=
  Array.ofFn (n := 693) fun x => invT 693 ((tvWordTabWith TT) W[x.val]!)

@[noinline, expose] def wordsOKWith (TT : Array Table) (W : Array (List Nat)) (gI : Array Table) : Bool :=
  W.size == 693 && gI.size == 693 &&
    allIn 0 693 fun x =>
      let w := W[x]!
      let T := (tvWordTabWith TT) w
      w.all (· < 693) && ap T 0 == x && invOK 693 T gI[x]!

@[noinline, expose] def rootOKWith (TT : Array Table) (P : Array Flags) (LT : Array (Array Nat)) (R : Flags) : Bool :=
  R.size == 693 &&
    allIn 0 693 (fun x =>
      let px := P[x]!
      allIn 0 693 fun y => !(decide (x < y) && px[y]!) ||
        (let c := (LT[x * 693 + y]!.toList.filter (R[·]!)).length; c == 0 || c == 2)) &&
    (members R).all fun x => let T := TT[x]!; allIn 0 693 fun q => R[q]! == R[ap T q]!

@[noinline, expose] def mkCtxWith (TT : Array Table) (P : Array Flags) (W : Array (List Nat)) (lam : Array Flags) :
    HCtx :=
  { P := P, pl := perpLists P, lam := lam,
    lamIdx := Array.ofFn (n := 693) fun p => filterRange (fun j => lam[j]![p.val]!) 1024 [],
    gI := (wordInvsWith TT) W }

@[noinline, expose] def hypChecksWith (TT : Array Table) (P : Array Flags) (LT : Array (Array Nat))
    (W : Array (List Nat)) (lam : Array Flags) (gs gi : Array Table)
    (o₀ o₁ o₂ : Array Flags × Array Nat × Array Nat) : Bool :=
  let C := (mkCtxWith TT) P W lam
  let H := o₀.1 ++ o₁.1 ++ o₂.1
  let ix := famIndex H
  lamOK P LT lam && (wordsOKWith TT) W C.gI &&
    (rootOKWith TT) P LT (rootFlags 1) && (rootOKWith TT) P LT (rootFlags 2) && (rootOKWith TT) P LT (rootFlags 3) &&
    hypOrbitOK (rootFlags 1) gs gi o₀ ix 0 && hypOrbitOK (rootFlags 2) gs gi o₁ ix 1408 &&
    hypOrbitOK (rootFlags 3) gs gi o₂ ix 2816 && famOK H ix && searchOK C H ix 40

@[expose] def hypCertificateWith (TT : Array Table) (_ : Unit) : Bool :=
  let P := (perpTabWith TT) ()
  (hypChecksWith TT) P (lineTab P) ((gWordsWith TT) ()) ((lamTabWith TT) ()) (hypGens ()) (hypGensInv ()) (hypEnum 1)
    (hypEnum 2) (hypEnum 3)

@[noinline, expose] def xiImgWith (TT : Array Table) (H : Array Flags) (ix : Std.HashMap (Array UInt64) Nat) :
    Array (Array Nat) :=
  Array.ofFn (n := 1408) fun k =>
    let S := H[k.val]!
    let M := members S
    Array.ofFn (n := 693) fun f =>
      if S[f.val]! then k.val else findIn ix 4224 (packImg TT[f.val]! M)

@[noinline, expose] def xiImgOKWith (TT : Array Table) (H : Array Flags) (Im Iv : Array (Array Nat)) : Bool :=
  allIn 0 1408 fun k =>
    let S := H[k]!
    let M := members S
    let row := Im[k]!
    let irow := Iv[k]!
    irow.size == 1408 && allIn 0 693 (fun f => S[f]! ||
      (let i := row[f]!
       i < 1408 && i != k && irow[i]! == f && (let T := TT[f]!; let Si := H[i]!;
         M.all fun p => Si[ap T p]!))) &&
    allIn 0 1408 fun i => irow[i]! == 693 ||
      (let f := irow[i]!; f < 693 && !S[f]! && row[f]! == i)

@[noinline, expose] def xiChecksWith (TT : Array Table) (P : Array Flags) (H : Array Flags) : Bool :=
  let ix := famIndex H
  let Im := (xiImgWith TT) H ix
  let Iv := xiInv H Im
  let A := xiAdj Iv
  H.size == 4224 && (xiImgOKWith TT) H Im Iv && xiInterOK H A && perpCountOK P (rootFlags 1) &&
    perpCountOK P (rootFlags 2) && perpCountOK P (rootFlags 3) && xiDiamOK A && xiMuOK A

@[expose] def xiCertificateWith (TT : Array Table) (_ : Unit) : Bool :=
  (xiChecksWith TT) ((perpTabWith TT) ()) (hypSets 1 ++ hypSets 2 ++ hypSets 3)

theorem clIter_eq_with (k : Nat) : ∀ F, clIter k F = clIterWith (tvTabs ()) k F := by
  induction k with
  | zero => intro F; rfl
  | succ k ih => intro F; exact ih _

theorem polarLinesCertificate_eq_with (u : Unit) :
    polarLinesCertificate u = polarLinesCertificateWith (tvTabs ()) u := rfl

theorem deltaCertificate_eq_with (u : Unit) :
    deltaCertificate u = deltaCertificateWith (tvTabs ()) u := rfl

theorem lamOf_eq_with (lns : Array (Array Nat)) : lamOf lns = lamOfWith (tvTabs ()) lns := by
  simp only [lamOf, lamOfWith, clIter_eq_with]

theorem lamTab_eq_with (u : Unit) : lamTab u = lamTabWith (tvTabs ()) u := by
  simp only [lamTab, lamTabWith, lamOf_eq_with]

theorem perpTab_eq_with (u : Unit) : perpTab u = perpTabWith (tvTabs ()) u := rfl

theorem gWords_eq_with (u : Unit) : gWords u = gWordsWith (tvTabs ()) u := rfl

theorem hypChecks_eq_with (P : Array Flags) (LT : Array (Array Nat)) (W : Array (List Nat))
    (lam : Array Flags) (gs gi : Array Table) (o₀ o₁ o₂ : Array Flags × Array Nat × Array Nat) :
    hypChecks P LT W lam gs gi o₀ o₁ o₂ = hypChecksWith (tvTabs ()) P LT W lam gs gi o₀ o₁ o₂ :=
  rfl

theorem hypCertificate_eq_with (u : Unit) :
    hypCertificate u = hypCertificateWith (tvTabs ()) u := by
  unfold hypCertificate hypCertificateWith
  rw [perpTab_eq_with, gWords_eq_with, lamTab_eq_with, hypChecks_eq_with]

theorem xiCertificate_eq_with (u : Unit) :
    xiCertificate u = xiCertificateWith (tvTabs ()) u := rfl

end CFSG.Fischer.Native

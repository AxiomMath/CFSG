module

public import Certificates.Data.Kernel.ASVolI.K43K
public import Certificates.Data.Kernel.HMathieu.Bfs
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.KS.ASVolI

open CFSG.ASVolI.K43Data CFSG.KC.HMathieu CFSG.KC.Enum CFSG.KS CFSG.KS.MathieuAut
  CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

@[expose] noncomputable def k43Img (p : ℕ) : List ℕ := (List.range 24).map fun i => pg 5 (mask 5) p i

@[expose] def z0P : ℕ := 961898487845936524069599993584526741

@[expose] noncomputable def fixesOctP (p : ℕ) : Bool := octPts.all fun i => pg 5 (mask 5) p i == i

@[expose] noncomputable def centP (vz : List ℕ) (p : ℕ) : Bool :=
  vz.all fun m => actM (colsC11 (k43Img p)) m == m

@[expose] noncomputable def kIdxK (E : List ℕ) : List ℕ :=
  (List.range E.length).filter fun p => fixesOctP (E.getD p 0)

@[expose] noncomputable def dzIdxK (E : List ℕ) : List ℕ :=
  (List.range E.length).filter fun p => centP (vzMasks ()) (E.getD p 0)

@[expose] def z0IdxK (E : List ℕ) : ℕ := (E.findIdx? (· == z0P)).getD 0

@[expose] noncomputable def listsK (E : List ℕ) : Bool :=
  let ds := E.filter (centP (vzMasks ()))
  decide (z0IdxK E < E.length) && E.getD (z0IdxK E) 0 == z0P &&
  E.all (fun x => pc24 x z0P == pc24 z0P x) &&
  (E.filter fixesOctP).length == 16 && ds.length == 16 &&
  ds.all (fun x => ds.all fun y => pc24 x y == pc24 y x) &&
  ds.all (fun x => pc24 x x == E.getD 0 0) &&
  ds.all (fun x => fixesOctP x == (x == E.getD 0 0 || x == z0P))

@[expose] noncomputable def listsS : Bool :=
  vpK z0P && unpk z0P == z0Arr &&
  (w5Masks ()).length == 32 && (vzMasks ()).length == 16 && CFSG.Decide.bitsetNodup (combos w5Basis) &&
  arrMul z0Arr z0Arr == idArr && (List.range 24).any (fun i => z0Arr[i]! != i) &&
  vBase.all (vzMasks ()).contains &&
  fixesOct z0Arr && ((List.range 24).all fun j => (z0Arr[j]! == j) == octPts.contains j) &&
  unpk (pidn 24 5) == idArr

@[expose] noncomputable def f3K (E : List ℕ) : Bool :=
  (E.filter fixesOctP).all fun x => unpk x == idArr || f3Wit.any (fun kg => kg.1 == unpk x)

@[expose] def f3S : Bool :=
  f3Wit.all fun kg => inAutK kg.2 && permM kg.2 e0mask == e0mask && arrConj kg.2 z0Arr == kg.1

@[expose] def moColsK : List (List ℕ) := moGens.map fun a => colsC11 a.toList

@[expose] def applyWordK (w : List ℕ) (m : ℕ) : ℕ :=
  w.foldr (fun g acc => actM (moColsK.getD g []) acc) m

@[expose] def indep6B (cands : List ℕ) : Bool :=
  let bs := pick6 cands
  bs.length == 6 && CFSG.Decide.bitsetNodup (combos bs)

@[expose] def f4Pred (m : ℕ) : Bool :=
  (w5Masks ()).contains m || indep6B ((wordPool 10 2).map fun w => applyWordK w m)

@[expose] def f4Slice (i : ℕ) : Bool := (List.range' (64 * i) 64).all f4Pred

@[expose] def f4S : Bool :=
  moGens.length == 10 && moGens.all fun g => g.size == 24 && inAutK g && permM g e0mask == e0mask

end CFSG.KS.ASVolI

end

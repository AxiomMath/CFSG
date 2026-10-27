module

public import Certificates.Data.ASVolIK43
public import Certificates.Data.Kernel.HMathieu.Orb
public import Certificates.Data.Kernel.MathieuAut.ColsK

public section

namespace CFSG.KS.ASVolI

open CFSG.ASVolI.K43Data CFSG.KC.HMathieu CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code

abbrev K43St := Array (ℕ × ℕ × ℕ) × KT

@[expose] def k43Inner (step : ℕ → ℕ → ℕ) (y h : ℕ) : List ℕ → K43St → K43St
  | [], s => s
  | g :: gs, s =>
    if s.2.mem (step g y) = true then k43Inner step y h gs s
    else k43Inner step y h gs (s.1.push (step g y, h, g), s.2.ins (step g y))

@[expose] def k43Outer (step : ℕ → ℕ → ℕ) (ngen : ℕ) : ℕ → ℕ → K43St → K43St
  | 0, _, s => s
  | f + 1, h, s =>
    if h < s.1.size then
      k43Outer step ngen f (h + 1) (k43Inner step s.1[h]!.1 h (List.range' 0 ngen) s)
    else s

@[expose] def bfsTableK (step : ℕ → ℕ → ℕ) (ngen x0 cap : ℕ) : K43St :=
  k43Outer step ngen cap 0 (#[(x0, 0, 0)], KT.leaf.ins x0)

structure QSt where
  front : List ℕ
  back : List ℕ
  cnt : ℕ
  tree : KT

@[expose] def qInner (step : ℕ → ℕ → ℕ) (y : ℕ) : List ℕ → QSt → QSt
  | [], q => q
  | g :: gs, q =>
    if q.tree.mem (step g y) = true then qInner step y gs q
    else qInner step y gs ⟨q.front, step g y :: q.back, q.cnt + 1, q.tree.ins (step g y)⟩

@[expose] def qOuter (step : ℕ → ℕ → ℕ) (ngen : ℕ) : ℕ → QSt → QSt
  | 0, q => q
  | f + 1, ⟨y :: fr, bk, c, t⟩ => qOuter step ngen f (qInner step y (List.range' 0 ngen) ⟨fr, bk, c, t⟩)
  | f + 1, ⟨[], bk, c, t⟩ =>
    match bk.reverse with
    | [] => ⟨[], bk, c, t⟩
    | y :: fr => qOuter step ngen f (qInner step y (List.range' 0 ngen) ⟨fr, [], c, t⟩)

@[expose] def bfsQ (step : ℕ → ℕ → ℕ) (ngen x0 cap : ℕ) : QSt :=
  qOuter step ngen cap ⟨[x0], [], 1, KT.leaf.ins x0⟩

@[expose] def octMissK (t : KT) : ℕ :=
  treeSumN (fun a => if popc 24 a == 8 && !(t.mem a) then 1 else 0) Bmask 12 0

@[expose] def octCols : List (List ℕ) := gensK.map permCols

@[expose] def octStepK (g y : ℕ) : ℕ := actM (octCols.getD g []) y

@[expose] def octOKK : Bool :=
  gensK.all inAutK && octPts.all (· < 24) && octPts.Nodup && octPts.length == 8 &&
    octMissK (bfsQ octStepK gensK.length e0mask 100000).tree == 0

@[expose] def ptStep (i g y : ℕ) : ℕ := ((ptGens[i]!)[g]!)[y]!

@[expose] def ptChainK : Bool :=
  ptBase.length == 6 && ptGens.length == 6 && ptBase.all (· < 24) &&
  (List.range 6).all fun i =>
    (ptGens[i]!).all (fun g => inAutK g && (ptBase.take i).all (fun b => g[b]! == b) &&
      (List.range 24).all fun y => decide (g[y]! < 24)) &&
    (bfsQ (ptStep i) (ptGens[i]!).length ptBase[i]! 1000).cnt == [24, 23, 22, 21, 20, 3][i]!

@[expose] def vCols (i : ℕ) : List (List ℕ) := (vGens[i]!).map fun a => colsC11 a.toList

@[expose] def vStepK (i g y : ℕ) : ℕ := actM ((vCols i).getD g []) y

@[expose] def vecChainK : Bool :=
  vBase.length == 3 && vGens.length == 3 && vBase.all (· < 2048) &&
  (List.range 3).all fun i =>
    (vGens[i]!).all (fun g => g.size == 24 && inAutK g &&
      (vBase.take i).all fun b => actC11 g b == b) &&
    (bfsQ (vStepK i) (vGens[i]!).length vBase[i]! 5000).cnt == [759, 280, 72][i]!

end CFSG.KS.ASVolI

end

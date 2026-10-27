module

public import Certificates.Data.ASVolIK43
public import Certificates.Data.Kernel.HMathieu.Tab
public import Certificates.Data.Kernel.HMathieu.Orb
public import Certificates.Data.Kernel.MathieuAut.InAutK
public import CFSG.Mathlib.Decide.Nodup

public section

namespace CFSG.KS.ASVolI

open CFSG.ASVolI.K43Data CFSG.KC.HMathieu CFSG.KS.MathieuAut CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def k78fL : List ℕ → (List ℕ → Bool) → Bool
  | [], k => k []
  | x :: xs, k => strictB x fun x' => k78fL xs fun xs' => k (x' :: xs')

@[expose] def k78pairs : List ℕ → List (ℕ × ℕ)
  | a :: b :: l => (a, b) :: k78pairs l
  | _ => []

@[expose] def k78pk (a : Array ℕ) : ℕ := a.toList.foldr (fun x acc => x + 32 * acc) 0

@[expose] noncomputable def k78pkOK (a : Array ℕ) : Bool := unpk (k78pk a) == a && vpK (k78pk a)

@[expose] noncomputable def k78id : ℕ := pidn 24 5

@[expose] def k78z0 : ℕ := k78pk z0Arr

@[expose] noncomputable def k78act (e m : ℕ) : ℕ := actP κCCols liftCCols e m

@[expose] noncomputable def k78cols (e : ℕ) : List ℕ := matOf 11 (k78act e)

@[expose] def k78z0c : List ℕ := matOf 11 (actC11 z0Arr)

@[expose] def k78quad (fa fb : ℕ → ℕ) : Bool :=
  (List.range 11).all fun j =>
    let w := fb (2 ^ j) ^^^ 2 ^ j
    fa w == w

@[expose] def k78dm (f : ℕ → ℕ) : List ℕ := (List.range 11).map fun j => f (2 ^ j) ^^^ 2 ^ j

@[expose] def k78indep6 (cands : List ℕ) : Bool :=
  let bs := pick6 cands
  bs.length == 6 && CFSG.Decide.bitsetNodup (combos bs) && bs.all cands.contains

@[expose] noncomputable def k78fixOct (e : ℕ) : Bool := octPts.all fun i => pg 5 (mask 5) e i == i

@[expose] noncomputable def k78inD (vz : List ℕ) (e : ℕ) : Bool := vz.all fun m => k78act e m == m

@[expose] def k78span (vz vb : List ℕ) : Bool := vb.all vz.contains && vz.all (combos vb).contains

@[expose] def k78tree (E : List ℕ) : KT := E.foldl KT.ins KT.leaf

@[expose] noncomputable def sylK (E : List ℕ) : Bool :=
  (sylConj.all fun c => inAutK c && arrMul c z0Arr == arrMul z0Arr c && k78pkOK c &&
    k78pkOK (invArr c)) &&
  k78fL (vzMasks ()) fun vz =>
  k78fL (pick6 vz) fun vb =>
  k78span vz vb &&
  k78fL (E.filter k78fixOct) fun ks =>
  k78fL (E.filter (k78inD vb)) fun ds =>
  k78fL (sylConj.flatMap fun c => [k78pk (invArr c), k78pk c]) fun cs =>
  E.all fun e =>
    !((k78pairs cs).all fun c => (k78tree E).mem (pc24 (pc24 c.1 e) c.2)) ||
      ks.any fun k => ds.any fun d => pc24 k d == e

@[expose] noncomputable def classK (E : List ℕ) : Bool :=
  k78pkOK z0Arr &&
  classWit.all (fun xg =>
    inAutK xg.1 && inAutK xg.2 && arrMul xg.2 z0Arr == arrMul z0Arr xg.2 &&
      (arrConj xg.2 (classWit[0]!).1 == xg.1 || arrConj xg.2 (classWit[0]!).1 == arrMul xg.1 z0Arr) &&
      k78pkOK xg.1) &&
  k78fL (vzMasks ()) fun vz =>
  k78fL (pick6 vz) fun vb =>
  k78span vz vb &&
  k78fL k78z0c fun cz =>
  k78fL (classWit.map (k78pk ·.1)) fun ws =>
  strictB k78id fun i0 =>
  strictB k78z0 fun z =>
  k78fL (E.filter (k78inD vb)) fun ds =>
  (ds.filter fun e => e != i0 && e != z).length == 14 &&
  E.all (fun e =>
    !(pc24 e e == i0 && e != i0 && e != z && k78quad (actM cz) (k78act e)) || k78inD vb e) &&
  (ds.filter fun e => e != i0 && e != z).all ws.contains

@[expose] noncomputable def modxK (vz cz fz ds : List ℕ) (i0 z e : ℕ) : Bool :=
  k78fL (k78cols e) fun cx =>
  strictB (pc24 e z) fun exz =>
  k78fL (k78dm (actM cx)) fun dxm =>
  k78fL (ds.filter fun p => k78quad (actM (k78cols p)) (actM cx)) fun stab =>
  stab.all [i0, e, z, exz].contains && [i0, e, z, exz].all stab.contains &&
  (fz.filter fun m => actM cx m == m).length == 64 &&
  [actM cx, actM cz, k78act exz].all (fun fy => k78quad (actM cx) fy && k78quad (actM cz) fy) &&
  k78indep6 (dxm ++ k78dm (actM cz)) && k78indep6 (vz ++ dxm)

@[expose] noncomputable def modK (E : List ℕ) : Bool :=
  k78pkOK z0Arr &&
  k78fL (vzMasks ()) fun vz =>
  k78fL (pick6 vz) fun vb =>
  k78span vz vb &&
  k78fL k78z0c fun cz =>
  k78fL ((List.range 2048).filter fun m => actM cz m == m) fun fz =>
  strictB k78id fun i0 =>
  strictB k78z0 fun z =>
  k78fL (E.filter (k78inD vb)) fun ds =>
  vz.all (combos (k78dm (actM cz))).contains &&
  (List.range 2048).all (fun m => vz.contains (actM cz m ^^^ m)) &&
  ds.all fun e => e == i0 || e == z || modxK vz cz fz ds i0 z e

end CFSG.KS.ASVolI

end

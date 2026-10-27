module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.KC.Ssa3

open CFSG.KC.Loop CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

structure SData where
  nk : List Nat
  na : List Nat
  nb : List Nat
  ns : List Nat
  opn : List Nat
  fv : List Nat
  cb : List Nat
  qb : List Nat
  qk : List Nat
  qx : List Nat
  qy : List Nat
  qt : List Nat
  qf : List Nat

structure Ar where
  mul : Nat → Nat → Nat
  one : Nat
  sa : Nat
  sb : Nat
  mt : Nat → Nat
  d : Nat
  n : Nat
  rm : Nat

@[expose] def pidS (D : SData) (y e x : Nat) : Bool :=
  bif Nat.beq e 0 then Nat.beq x 2 else bif Nat.beq e 1 then Nat.beq x y else
    Nat.ble 3 x && Nat.beq (D.nk.getD (x - 3) 1) e && Nat.beq (D.na.getD (x - 3) 0) y

@[expose] def mulS (D : SData) (y z x : Nat) : Bool :=
  Nat.ble 3 x && Nat.beq (D.nk.getD (x - 3) 1) 0 && Nat.beq (D.na.getD (x - 3) 0) y &&
    Nat.beq (D.nb.getD (x - 3) 0) z

@[expose] def progS (D : SData) : List Op → List Nat → List Nat → Bool
  | [], [], V => V == D.fv
  | .mul i j k :: p, x :: xs, V =>
    mulS D (V.getD i 0) (V.getD j 0) x && progS D p xs (V.set k x)
  | .pow e i k :: p, x :: xs, V => pidS D (V.getD i 0) e x && progS D p xs (V.set k x)
  | _, _, _ => false

@[expose] def nodesS : Nat → List Nat → List Nat → List Nat → List Nat → Bool
  | _, [], [], [], [] => true
  | j, k :: ks, a :: as, b :: bs, _ :: ss =>
    Nat.blt a (3 + j) && Nat.blt b (3 + j) &&
      (Nat.beq k 0 || (Nat.ble 2 k && Nat.blt k 65536)) && nodesS (j + 1) ks as bs ss
  | _, _, _, _, _ => false

@[expose] def ascS : List Nat → Bool
  | a :: b :: l => Nat.ble a b && ascS (b :: l)
  | _ => true

@[expose] def boundsS (l : List Nat) (m : Nat) : Bool :=
  Nat.beq (l.headD 1) 0 && Nat.beq (l.getLastD 0) m && ascS l

@[expose] def structS (D : SData) : Bool :=
  nodesS 0 D.nk D.na D.nb D.ns && boundsS D.cb D.nk.length && boundsS D.qb D.qk.length &&
    Nat.beq D.qb.length D.cb.length && Nat.beq D.qx.length D.qk.length &&
    Nat.beq D.qy.length D.qk.length && Nat.beq D.qt.length D.qk.length &&
    Nat.beq D.qf.length D.qk.length

@[expose] def ssaOK (D : SData) (prog : List Op) (n : Nat) : Bool :=
  Nat.ble 2 n && prog.all (Op.lt n) && structS D &&
    progS D prog D.opn ((List.range n).map fun r => Nat.min r 2)

@[expose] noncomputable def recV (R : Ar) (D : SData) (x : Nat) : Nat :=
  bif Nat.beq x 0 then R.sa else bif Nat.beq x 1 then R.sb else bif Nat.beq x 2 then R.one else
    R.mt (Nat.sub (D.ns.getD (x - 3) 0) 1)

@[expose] def availS (D : SData) (lo x : Nat) : Bool :=
  Nat.blt x 3 || (Nat.blt x (3 + lo) && !Nat.beq (D.ns.getD (x - 3) 0) 0)

@[expose] noncomputable def getV (R : Ar) (D : SData) (lo : Nat) (L : List Nat) (x : Nat) : Nat :=
  bif Nat.ble (3 + lo) x then L.getD (x - (3 + lo)) 0 else recV R D x

@[expose] noncomputable def powT (mul : Nat → Nat → Nat) (one X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Bool → Nat) (fun acc st => bif st then acc else one)
    (fun i ih acc st =>
      bif st then
        strictN (mul acc acc) fun s =>
          bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then strictN (mul s X) fun t => ih t true
          else ih s true
      else bif Nat.beq (Nat.land (Nat.shiftRight e i) 1) 1 then ih X true else ih acc false)
    16 one false

@[expose] noncomputable def runC (R : Ar) (D : SData) (lo : Nat) (fin : List Nat → Nat) (m : Nat) :
    Nat → List Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat → Nat) (fun _ L => fin L)
    (fun _ ih j L =>
      bif (Nat.ble (3 + lo) (D.na.getD j 0) || availS D lo (D.na.getD j 0)) &&
          (!Nat.beq (D.nk.getD j 1) 0 || Nat.ble (3 + lo) (D.nb.getD j 0) ||
            availS D lo (D.nb.getD j 0)) then
        strictN (bif Nat.beq (D.nk.getD j 1) 0 then
            R.mul (getV R D lo L (D.na.getD j 0)) (getV R D lo L (D.nb.getD j 0))
          else powT R.mul R.one (getV R D lo L (D.na.getD j 0)) (D.nk.getD j 1)) fun v =>
          bif Nat.beq (D.ns.getD j 0) 0 || Nat.beq v (R.mt (Nat.sub (D.ns.getD j 0) 1)) then
            ih (j + 1) (L ++ [v])
          else 0
      else 0) m

@[expose] noncomputable def rowDiff (R : Ar) (X Y t : Nat) : Bool :=
  !(Nat.beq (Nat.land (Nat.shiftRight X (R.d * t)) R.rm) (Nat.land (Nat.shiftRight Y (R.d * t)) R.rm) &&
    Nat.beq (Nat.land (Nat.shiftRight X (R.n + R.d * t)) R.rm)
      (Nat.land (Nat.shiftRight Y (R.n + R.d * t)) R.rm))

@[expose] def endS (D : SData) (lo hi x : Nat) : Bool :=
  availS D lo x || (Nat.ble (3 + lo) x && Nat.blt x (3 + hi))

@[expose] noncomputable def cmpOK (R : Ar) (D : SData) (lo hi : Nat) (L : List Nat) (q : Nat) :
    Bool :=
  endS D lo hi (D.qx.getD q 0) && endS D lo hi (D.qy.getD q 0) &&
    bif Nat.beq (D.qk.getD q 0) 0 then
      Nat.beq (getV R D lo L (D.qx.getD q 0)) (getV R D lo L (D.qy.getD q 0))
    else Nat.blt (D.qt.getD q 0) R.d &&
      rowDiff R (getV R D lo L (D.qx.getD q 0)) (getV R D lo L (D.qy.getD q 0)) (D.qt.getD q 0)

@[expose] noncomputable def chunkOK (R : Ar) (D : SData) (c : Nat) : Bool :=
  Nat.beq (runC R D (D.cb.getD c 0)
    (fun L => bif (List.range' (D.qb.getD c 0) (D.qb.getD (c + 1) 0 - D.qb.getD c 0)).all
        (cmpOK R D (D.cb.getD c 0) (D.cb.getD (c + 1) 0) L) then 1 else 0)
    (D.cb.getD (c + 1) 0 - D.cb.getD c 0) (D.cb.getD c 0) []) 1

@[expose] def widS (D : SData) : Word → Nat → Bool
  | [], x => Nat.beq x 2
  | [(r, e)], x => pidS D (D.fv.getD r 0) e x
  | (r, e) :: w, x => mulS D (D.na.getD (x - 3) 0) (D.nb.getD (x - 3) 0) x &&
      pidS D (D.fv.getD r 0) e (D.na.getD (x - 3) 0) && widS D w (D.nb.getD (x - 3) 0)

@[expose] def factS (D : SData) (n : Nat) (q : Nat) : MFact → Bool
  | .ord r e => Nat.beq (D.qk.getD q 1) 0 && Nat.blt r n && Nat.blt 0 e &&
      pidS D (D.fv.getD r 0) e (D.qx.getD q 0) && Nat.beq (D.qy.getD q 0) 2
  | .conj h u w => Nat.beq (D.qk.getD q 1) 0 && Nat.blt h n && wordLt n u && wordLt n w &&
      mulS D (D.fv.getD h 0) (D.nb.getD (D.qx.getD q 0 - 3) 0) (D.qx.getD q 0) &&
      widS D u (D.nb.getD (D.qx.getD q 0 - 3) 0) &&
      mulS D (D.na.getD (D.qy.getD q 0 - 3) 0) (D.fv.getD h 0) (D.qy.getD q 0) &&
      widS D w (D.na.getD (D.qy.getD q 0 - 3) 0)
  | .ne w₁ w₂ t => !Nat.beq (D.qk.getD q 0) 0 && wordLt n w₁ && wordLt n w₂ &&
      Nat.beq (D.qt.getD q 0) t && widS D w₁ (D.qx.getD q 0) && widS D w₂ (D.qy.getD q 0)
  | .eq w₁ w₂ => Nat.beq (D.qk.getD q 1) 0 && wordLt n w₁ && wordLt n w₂ &&
      widS D w₁ (D.qx.getD q 0) && widS D w₂ (D.qy.getD q 0)

@[expose] def cmpsS (D : SData) (n : Nat) (facts : List MFact) : Bool :=
  (List.range D.qk.length).all fun q =>
    Nat.blt (D.qf.getD q 0) facts.length && factS D n q (facts.getD (D.qf.getD q 0) (.eq [] []))

end CFSG.KC.Ssa3

end

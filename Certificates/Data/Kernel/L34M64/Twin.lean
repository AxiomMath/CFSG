module

public import CFSG.Quasithin.Vol2.Ch9L34M64D
public import Certificates.Data.Kernel.HMathieu.FixTab

public section

namespace CFSG.KC.L34M64

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34M

@[expose] noncomputable def ln (P k : ℕ) : ℕ := Nat.land (Nat.shiftRight P (Nat.mul 2 k)) 3

@[expose] noncomputable def mulT (a b : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight 2625168384 (Nat.mul 2 (Nat.add (Nat.mul 4 a) b))) 3

@[expose] noncomputable def pk (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec 0 (fun k acc => Nat.add acc (Nat.shiftLeft (f k) (Nat.mul 2 k))) n

@[expose] noncomputable def xr (f : ℕ → ℕ) (n : ℕ) : ℕ := Nat.rec 0 (fun k acc => Nat.xor acc (f k)) n

@[expose] noncomputable def mulP (P Q : ℕ) : ℕ :=
  pk (fun p => xr (fun l => mulT (ln P (Nat.add (Nat.mul 8 (Nat.div p 8)) l))
    (ln Q (Nat.add (Nat.mul 8 l) (Nat.mod p 8)))) 8) 64

@[expose] noncomputable def bt (m k : ℕ) : ℕ := Nat.land (Nat.shiftRight m k) 1

@[expose] noncomputable def upc (m i j : ℕ) : ℕ :=
  Nat.add (bt m (Nat.add (Nat.mul 8 i) j)) (Nat.mul 2 (bt m (Nat.add (Nat.mul 8 j) i)))

@[expose] noncomputable def ycK (m i j : ℕ) : ℕ :=
  Bool.rec (Bool.rec (bt m (Nat.add (Nat.mul 8 i) i)) (mulT (upc m j i) (upc m j i)) (Nat.blt j i))
    (upc m i j) (Nat.blt i j)

@[expose] noncomputable def yP (m : ℕ) : ℕ := pk (fun p => ycK m (Nat.div p 8) (Nat.mod p 8)) 64

@[expose] noncomputable def starP (P : ℕ) : ℕ :=
  pk (fun p => mulT (ln P (Nat.add (Nat.mul 8 (Nat.mod p 8)) (Nat.div p 8)))
    (ln P (Nat.add (Nat.mul 8 (Nat.mod p 8)) (Nat.div p 8)))) 64

@[expose] noncomputable def cjP (P : ℕ) : ℕ := pk (fun p => mulT (ln P p) (ln P p)) 64

@[expose] noncomputable def mbit (Z r c : ℕ) : ℕ :=
  Bool.rec (Bool.rec (Nat.land (ln Z (Nat.add (Nat.mul 8 r) r)) 1)
      (Nat.shiftRight (ln Z (Nat.add (Nat.mul 8 c) r)) 1) (Nat.blt c r))
    (Nat.land (ln Z (Nat.add (Nat.mul 8 r) c)) 1) (Nat.blt r c)

@[expose] noncomputable def maskP (Z : ℕ) : ℕ :=
  Nat.rec 0 (fun p acc => Nat.add acc (Nat.shiftLeft (mbit Z (Nat.div p 8) (Nat.mod p 8)) p)) 64

@[expose] noncomputable def actP (P m : ℕ) : ℕ := maskP (mulP (mulP P (yP m)) (starP P))

@[expose] noncomputable def fldP (m : ℕ) : ℕ := maskP (cjP (yP m))

@[expose] noncomputable def colsChk (F : ℕ → ℕ) (L : List ℕ) : ℕ → Bool :=
  List.rec (fun j => Nat.beq j 64)
    (fun c _ ih j => Bool.rec false (ih (Nat.succ j)) (Nat.beq (F (Nat.shiftLeft 1 j)) c)) L

@[expose] noncomputable def allB (g : ℕ → Bool) (n : ℕ) : Bool :=
  Nat.rec true (fun k acc => Bool.rec false (g k) acc) n

@[expose] def entC (A : Matrix (Fin 8) (Fin 8) F4) (p : ℕ) : ℕ :=
  if h : p < 64 then (A (row8 ⟨p, h⟩) (col8 ⟨p, h⟩)).code.val else 0

@[expose] noncomputable def codesChk (P : ℕ) (A : Matrix (Fin 8) (Fin 8) F4) : Bool :=
  allB (fun p => Nat.beq (ln P p) (entC A p)) 64

@[expose] noncomputable def matChk (R : Matrix (Fin 8) (Fin 8) F4) (P : ℕ) (L : List ℕ) : Bool :=
  codesChk P R && colsChk (actP P) L 0

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def compK (cs ds : List ℕ) : List ℕ := ds.map (actK cs)

@[expose] noncomputable def isInvK (cs : List ℕ) : Bool :=
  (List.range 64).all (fun i => actK cs (actK cs (2 ^ i)) == 2 ^ i) && !(cs == idC64)

@[expose] noncomputable def pickWitK (n r : ℕ) (cs : List ℕ) : List ℕ :=
  (List.range n).foldl (fun ws i =>
    if ws.length < r && decide (combos ((ws ++ [2 ^ i]).map fun w => actK cs w ^^^ w)).Nodup
    then ws ++ [2 ^ i] else ws) []

@[expose] noncomputable def nonQuadK (n : ℕ) (cs ds : List ℕ) : Bool :=
  (List.range n).any fun i => actK cs (actK ds (2 ^ i) ^^^ 2 ^ i) != (actK ds (2 ^ i) ^^^ 2 ^ i)

@[expose] noncomputable def rankOKK (r n : ℕ) (cs ws : List ℕ) : Bool :=
  decide (r ≤ ws.length) && AllLt n ws && decide (combos (ws.map fun w => actK cs w ^^^ w)).Nodup

@[expose] noncomputable def chk1K (n : ℕ) (dat : List (List ℕ × List ℕ)) : Bool :=
  dat.all (fun d => AllLt n d.1 && rankOKK 3 n d.1 d.2) &&
    dat.all fun d => dat.all fun d' => d.1 == d'.1 || nonQuadK n d.1 d'.1

end CFSG.KC.L34M64

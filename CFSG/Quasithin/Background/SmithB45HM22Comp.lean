module

public import CFSG.Quasithin.Background.SmithB45HM22Pack
public import CFSG.Quasithin.Background.SmithB45M22HatModel

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22

@[expose] def packColOf {m n : ℕ} (A : Matrix (Fin m) (Fin n) FieldFour) (j : Fin n) : PV :=
  (List.finRange m).foldr (fun (i : Fin m) acc => PV.add (PV.single (i : ℕ) (A i j)) acc) (0, 0)

@[expose] def PM.ofMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) FieldFour) : PM :=
  (List.finRange n).map (packColOf A)

theorem PM.length_ofMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) FieldFour) :
    (PM.ofMat A).length = n := by
  simp [PM.ofMat]

theorem get_packColOf {m n : ℕ} (A : Matrix (Fin m) (Fin n) FieldFour) (j : Fin n) (i : Fin m) :
    (packColOf A j).get i = A i j := by
  rw [packColOf, PV.get_foldr_add]
  simp only [PV.get_single]
  rw [← List.sum_toFinset _ (List.nodup_finRange m), List.toFinset_finRange]
  simp only [Fin.val_inj]
  rw [Finset.sum_ite_eq Finset.univ i, ite_eq_left (Finset.mem_univ i)]

theorem PM.toMat_ofMat {m n : ℕ} (A : Matrix (Fin m) (Fin n) FieldFour) :
    PM.toMat m n (PM.ofMat A) = A := by
  funext i j
  simp only [PM.toMat, PM.col, PM.ofMat]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_finRange]
  exact get_packColOf A _ i

@[expose] def n1P : PM := PM.ofMat hatM22N1

@[expose] def n2P : PM := PM.ofMat hatM22N2

@[expose] def n2iP : PM := PM.mul n2P (PM.mul n2P n2P)

@[expose] def pGen (z : ℤ) : PM :=
  if z = 2 then n2P else if z = -2 then n2iP else n1P

@[expose] def pWord : List ℤ → PM
  | [] => PM.idm 6
  | z :: w => PM.mul (pGen z) (pWord w)

@[expose] def invW (w : List ℤ) : List ℤ := (w.map fun z => -z).reverse

@[expose] def cosetW : List (List ℤ) :=
  [[], [2, 1], [2, 2], [2, 2, 2, 1], [2, 1, 2, 2, 2, 1], [1, 2], [2, 2, 1, 2], [1, 2, 1],
    [1, 2, 2, 2, 1, 2, 1], [2, 2, 2, 1, 2, 1], [2, 1, 2], [1, 2, 2, 2, 1], [1], [2, 1, 2, 1],
    [2, 2, 2, 1, 2], [1, 2, 2], [1, 2, 2, 1, 2], [2, 2, 1], [2, 1, 2, 2, 1, 2], [2, 2, 1, 2, 1],
    [2, 2, 2], [2]]

@[expose] def sigAL : List ℕ :=
  [12, 7, 15, 11, 4, 21, 16, 1, 9, 8, 13, 3, 0, 10, 14, 2, 6, 17, 18, 19, 20, 5]

@[expose] def sigBL : List ℕ :=
  [21, 17, 20, 12, 11, 10, 14, 13, 8, 7, 6, 4, 1, 19, 5, 15, 18, 3, 16, 9, 0, 2]

@[expose] def sigF (b : Bool) (k : ℕ) : ℕ := (if b then sigBL else sigAL).getD k 0

@[expose] def gcode (b : Bool) : ℤ := if b then 2 else 1

@[expose] def hword (b : Bool) (k : ℕ) : List ℤ :=
  invW (cosetW.getD (sigF b k) []) ++ [gcode b] ++ cosetW.getD k []

@[expose] def hatM22R0 : Matrix (Fin 6) (Fin 3) FieldFour :=
  untab #v[#v[0, 0, 0], #v[1, 0, 0], #v[0, 0, 0], #v[0, 0, 0], #v[0, 1, 0], #v[0, 0, 1]]

@[expose] def hatM22B8 : Matrix (Fin 9) (Fin 8) FieldFour :=
  untab #v[#v[1, 1, 0, 0, 0, 0, 0, 0], #v[0, 0, 1, 0, 0, 0, 0, 0], #v[0, 0, 0, 1, 0, 0, 0, 0],
    #v[0, 0, 0, 0, 1, 0, 0, 0], #v[1, 0, 0, 0, 0, 0, 0, 0], #v[0, 0, 0, 0, 0, 1, 0, 0],
    #v[0, 0, 0, 0, 0, 0, 1, 0], #v[0, 0, 0, 0, 0, 0, 0, 1], #v[0, 1, 0, 0, 0, 0, 0, 0]]

@[expose] def hatM22P8 : Matrix (Fin 8) (Fin 9) FieldFour :=
  untab #v[#v[0, 0, 0, 0, 1, 0, 0, 0, 0], #v[0, 0, 0, 0, 0, 0, 0, 0, 1],
    #v[0, 1, 0, 0, 0, 0, 0, 0, 0], #v[0, 0, 1, 0, 0, 0, 0, 0, 0], #v[0, 0, 0, 1, 0, 0, 0, 0, 0],
    #v[0, 0, 0, 0, 0, 1, 0, 0, 0], #v[0, 0, 0, 0, 0, 0, 1, 0, 0], #v[0, 0, 0, 0, 0, 0, 0, 1, 0]]

@[expose] def blk3a (w : List ℤ) : PM :=
  PM.mul (PM.mul (PM.ofMat (hatM22L 0)) (pWord w)) (PM.ofMat (hatM22B 0))

@[expose] def blk3b (w : List ℤ) : PM :=
  PM.mul (PM.mul (PM.ofMat (hatM22F 0)) (pWord w)) (PM.ofMat hatM22R0)

@[expose] def blk9 (w : List ℤ) : PM :=
  PM.kron 3 3 (PM.transp 3 (blk3a (invW w))) (PM.frob (blk3a w))

@[expose] def blk8 (w : List ℤ) : PM :=
  PM.mul (PM.mul (PM.ofMat hatM22P8) (PM.kron 3 3 (blk3a w) (PM.transp 3 (blk3a (invW w)))))
    (PM.ofMat hatM22B8)

@[expose] def blk24a (w : List ℤ) : PM :=
  PM.kron 8 3 (blk8 w) (PM.frob (PM.transp 3 (blk3a (invW w))))

@[expose] def blk24b (w : List ℤ) : PM :=
  PM.kron 3 8 (blk3a w) (PM.frob (blk8 w))

@[expose] def indP (blk : List ℤ → PM) (d : ℕ) (b : Bool) : PM :=
  (List.range 22).flatMap fun k =>
    (List.range d).map fun c => PV.shl ((PM.col (blk (hword b k)) c).trunc d) (d * sigF b k)

end CFSG.Quasithin.HM22

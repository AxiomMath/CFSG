module

public import Certificates.Data.G24IdentWit
public import CFSG.LieType.Multipliers.G24Bridge
public import CFSG.Timmesfeld.Exceptional.FiveFiveFive

public section

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Fischer CFSG.LieType.Multipliers.G24 CFSG.Certificates
open CFSG.Quasithin.St84.G24Wit
open CFSG.Quasithin.St84.G24Ident

variable {H : Type*} [Group H]

theorem toMat_evalP {n : ℕ} (φ : H →* GL (Fin 14) F4) (y : Fin n → H) (G : Array Mat)
    (hG : ∀ i : Fin n, toMat 14 (G.getD i.val one14) =
      ((φ (y i) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4)) (w : List (Fin n)) :
    toMat 14 (evalP G w) =
      ((φ ((w.map y).prod) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) := by
  induction w with
  | nil => simp [evalP, toMat_one14]
  | cons l w ih =>
    rw [show evalP G (l :: w) = mulArr 14 (G.getD l.val one14) (evalP G w) from rfl,
      toMat_mulArr, hG l, ih, List.map_cons, List.prod_cons, map_mul]
    rfl

private theorem toMat_foldl_mulArr_inv {n : ℕ} (φ : H →* GL (Fin 14) F4)
    (y : Fin n → H) (Gi : Array Mat)
    (hGi : ∀ i : Fin n, toMat 14 (Gi.getD i.val one14) =
      (((φ (y i))⁻¹ : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4))
    (w : List (Fin n)) (init : Mat) :
    toMat 14 (w.foldl (fun A l => mulArr 14 (Gi.getD l.val one14) A) init) =
      (((φ ((w.map y).prod))⁻¹ : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) *
        toMat 14 init := by
  induction w generalizing init with
  | nil => simp [toMat_one14]
  | cons l w ih =>
    show toMat 14 (List.foldl (fun A l => mulArr 14 (Gi.getD l.val one14) A)
      (mulArr 14 (Gi.getD l.val one14) init) w) = _
    rw [ih (mulArr 14 (Gi.getD l.val one14) init), toMat_mulArr, hGi l,
      List.map_cons, List.prod_cons, map_mul, mul_inv_rev]
    rw [Units.val_mul]
    group

theorem toMat_evalPInv {n : ℕ} (φ : H →* GL (Fin 14) F4) (y : Fin n → H) (Gi : Array Mat)
    (hGi : ∀ i : Fin n, toMat 14 (Gi.getD i.val one14) =
      (((φ (y i))⁻¹ : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4)) (w : List (Fin n)) :
    toMat 14 (evalPInv Gi w) =
      (((φ ((w.map y).prod))⁻¹ : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) := by
  rw [evalPInv]
  simpa [toMat_one14] using toMat_foldl_mulArr_inv φ y Gi hGi w one14

theorem toMat_evalL {n : ℕ} (φ : H →* GL (Fin 14) F4) (y : Fin n → H) (G : Array Mat × Array Mat)
    (hG1 : ∀ i : Fin n, toMat 14 (G.1.getD i.val one14) =
      ((φ (y i) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4))
    (hG2 : ∀ i : Fin n, toMat 14 (G.2.getD i.val one14) =
      (((φ (y i))⁻¹ : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4))
    (w : List (Fin n × Bool)) :
    toMat 14 (evalL G w) =
      ((φ (signedProd y w) : GL (Fin 14) F4) : Matrix (Fin 14) (Fin 14) F4) := by
  induction w with
  | nil => simp [evalL, signedProd, toMat_one14]
  | cons l w ih =>
    obtain ⟨i, s⟩ := l
    cases s
    · rw [show evalL G ((i, false) :: w) = mulArr 14 (G.2.getD i.val one14) (evalL G w) from rfl,
        toMat_mulArr, hG2 i, ih, signedProd_cons]
      simp
    · rw [show evalL G ((i, true) :: w) = mulArr 14 (G.1.getD i.val one14) (evalL G w) from rfl,
        toMat_mulArr, hG1 i, ih, signedProd_cons]
      simp

theorem toMat_frobArr (A : Mat) :
    toMat 14 (frobArr A) = (toMat 14 A).map fun x => x * x := by
  ext i j
  simp only [toMat, frobArr, Matrix.map_apply, Matrix.of_apply,
    Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rcases h : A[i.val]? with _ | r
  · simp [h]
  · simp only [Option.map_some, Option.getD_some, Array.getD_eq_getD_getElem?,
      Array.getElem?_map]
    rcases hr : r[j.val]? with _ | x <;> simp [hr]

theorem matsOf_fst (ws : List Word) (i : ℕ) :
    (matsOf ws).1.getD i one14 = wordArr (ws.getD i []) := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, matsOf]
  simp only [List.getElem?_toArray, List.getElem?_map]
  cases hh : ws[i]? with
  | none => rfl
  | some w => rfl

theorem matsOf_snd (ws : List Word) (i : ℕ) :
    (matsOf ws).2.getD i one14 = wordArr (ws.getD i []).reverse := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, matsOf]
  simp only [List.getElem?_toArray, List.getElem?_map]
  cases hh : ws[i]? with
  | none => rfl
  | some w => rfl

theorem wordArr_invW (w : List (Fin 6 × Bool)) :
    wordArr (invW w) = wordArr w.reverse := by
  have h : ∀ u : List (Fin 6 × Bool), wordArr (u.map fun l => (l.1, !l.2)) = wordArr u := by
    intro u
    induction u with
    | nil => rfl
    | cons l u ih =>
      simpa [wordArr] using congrArg (mulArr 14 (genArr l.1)) ih
  simpa [invW] using h w.reverse

theorem invW_eq_invWord {n : ℕ} (w : List (Fin n × Bool)) :
    invW w = CFSG.Timmesfeld.Moufang.Exc.invWord w := rfl

end CFSG.Quasithin.F112R.St84.G24M

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Quasithin.St84.G24DC.Native CFSG.Quasithin.St84.G24Ident

private theorem gBN_size : (gBN ()).size = 4 := rfl

private theorem wWords_length : wWords.length = 12 := rfl

private theorem wWords_row_length (i : ℕ) (hi : i < 12) : (wWords.getD i []).length = 4 := by
  interval_cases i <;> rfl

private theorem wImgN_size : (wImgN ()).size = 12 := by
  simp only [wImgN, List.size_toArray, List.length_map, wWords_length]

theorem gB_size : CFSG.Quasithin.St84.G24DC.gB.size = 4 := by
  rw [CFSG.Quasithin.St84.G24DC.gB, Array.size_map, gBN_size]

end CFSG.Quasithin.F112R.St84.G24M

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.Quasithin.St84.G24DC CFSG.Quasithin.St84.G24DC.Native
open CFSG.Quasithin.St84.G24Ident

theorem gB_getD (k : ℕ) (hk : k < 4) :
    gB.getD k CFSG.LieType.Multipliers.G24.one14 =
      Code.decMat ((Native.gBN ()).getD k Native.oneM) := by
  rw [gB, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rw [Array.getElem?_eq_getElem (by rwa [gBN_size]), Option.map_some,
    Option.getD_some]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rwa [gBN_size])]
  rfl

private theorem wImg_row (i : ℕ) (hi : i < 12) :
    (wImg ()).getD i #[] =
      ((Native.wWords.getD i []).map (Native.evalF (Native.gBN ()))).toArray.map
        Code.decMat := by
  rw [wImg, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rw [Array.getElem?_eq_getElem (by rwa [wImgN_size]), Option.map_some,
    Option.getD_some]
  simp only [Native.wImgN]
  rw [List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem (l := Native.wWords) (n := i) (d := [])
      (by rwa [wWords_length])]

theorem wImg_row_size (i : ℕ) (hi : i < 12) : ((wImg ()).getD i #[]).size = 4 := by
  rw [wImg_row i hi, Array.size_map, List.size_toArray, List.length_map,
    wWords_row_length i hi]

theorem wImg_getD (i k : ℕ) (hi : i < 12) (hk : k < 4) :
    ((wImg ()).getD i #[]).getD k CFSG.LieType.Multipliers.G24.one14 =
      Code.decMat (Native.evalF (Native.gBN ()) ((Native.wWords.getD i []).getD k [])) := by
  rw [wImg_row i hi, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  rw [Array.getElem?_eq_getElem (by
    rw [List.size_toArray, List.length_map, wWords_row_length i hi]
    exact hk),
    Option.map_some, Option.getD_some]
  rw [List.getElem_toArray, List.getElem_map,
    List.getD_eq_getElem (l := Native.wWords.getD i []) (n := k) (d := [])
      (by rwa [wWords_row_length i hi])]

end CFSG.Quasithin.F112R.St84.G24M

namespace CFSG.Quasithin.F112R.St84.G24M

open CFSG.LieType.Multipliers.G24 CFSG.Quasithin.St84.G24Wit CFSG.Quasithin.St84.G24Ident

theorem toMat_conjArr (g x g' : Mat) :
    toMat 14 (conjArr g x g') = toMat 14 g * toMat 14 x * toMat 14 g' := by
  simp only [conjArr, toMat_mulArr, mul_assoc]

end CFSG.Quasithin.F112R.St84.G24M

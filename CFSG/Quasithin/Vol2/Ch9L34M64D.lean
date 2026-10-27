module

public import CFSG.Quasithin.Vol2.Ch9L34M16

public section

namespace CFSG.Quasithin.H13.Ch9.L34M

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code

@[expose] def barM {n : ℕ} (Y : Matrix (Fin n) (Fin n) F4) : Matrix (Fin n) (Fin n) F4 := Y.map cj

@[expose] def IsHermM {n : ℕ} (Y : Matrix (Fin n) (Fin n) F4) : Prop := ∀ i j, Y j i = cj (Y i j)

theorem barM_apply {n : ℕ} (Y : Matrix (Fin n) (Fin n) F4) (i j : Fin n) :
    barM Y i j = cj (Y i j) := rfl

theorem barM_barM {n : ℕ} (Y : Matrix (Fin n) (Fin n) F4) : barM (barM Y) = Y := by
  ext i j
  exact cj_cj _

theorem barM_mul {n : ℕ} (Y Z : Matrix (Fin n) (Fin n) F4) : barM (Y * Z) = barM Y * barM Z :=
  Matrix.map_mul (f := (cjRing : F4 →+* F4))

theorem barM_add {n : ℕ} (Y Z : Matrix (Fin n) (Fin n) F4) : barM (Y + Z) = barM Y + barM Z := by
  ext i j
  exact cj_add _ _

theorem barM_one {n : ℕ} : barM (1 : Matrix (Fin n) (Fin n) F4) = 1 := by
  ext i j
  rw [barM_apply, one_apply]
  split_ifs
  · exact cj_one
  · exact cj_zero

theorem barM_transpose {n : ℕ} (Y : Matrix (Fin n) (Fin n) F4) : barM Yᵀ = (barM Y)ᵀ := rfl

theorem isHermM_conj {n : ℕ} (R : Matrix (Fin n) (Fin n) F4) {Y : Matrix (Fin n) (Fin n) F4}
    (hY : IsHermM Y) : IsHermM (R * Y * (barM R)ᵀ) := by
  have hY' : Yᵀ = barM Y := by
    ext i j
    exact hY i j
  have h : (R * Y * (barM R)ᵀ)ᵀ = barM (R * Y * (barM R)ᵀ) := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hY', barM_mul, barM_mul,
      ← barM_transpose, barM_barM, Matrix.mul_assoc]
  intro i j
  have := congrFun (congrFun h i) j
  rw [transpose_apply] at this
  exact this

theorem isHermM_barM {n : ℕ} {Y : Matrix (Fin n) (Fin n) F4} (hY : IsHermM Y) :
    IsHermM (barM Y) := by
  intro i j
  rw [barM_apply, barM_apply, hY i j]

@[expose] def pos8 (i j : Fin 8) : Fin 64 := ⟨8 * i.val + j.val, by omega⟩

@[expose] def herm8V (v : Fin 64 → ZMod 2) : Matrix (Fin 8) (Fin 8) F4 :=
  Matrix.of fun i j =>
    if i < j then mk (v (pos8 i j)) (v (pos8 j i))
    else if j < i then cj (mk (v (pos8 j i)) (v (pos8 i j)))
    else mk (v (pos8 i i)) 0

@[expose] def row8 (p : Fin 64) : Fin 8 := ⟨p.val / 8, by omega⟩

@[expose] def col8 (p : Fin 64) : Fin 8 := ⟨p.val % 8, by omega⟩

@[expose] def code8V (Y : Matrix (Fin 8) (Fin 8) F4) : Fin 64 → ZMod 2 := fun p =>
  if row8 p < col8 p then lo (Y (row8 p) (col8 p))
  else if col8 p < row8 p then hi (Y (col8 p) (row8 p))
  else lo (Y (row8 p) (row8 p))

theorem row8_pos8 (i j : Fin 8) : row8 (pos8 i j) = i := by
  apply Fin.ext
  simp only [row8, pos8]
  omega

theorem col8_pos8 (i j : Fin 8) : col8 (pos8 i j) = j := by
  apply Fin.ext
  simp only [col8, pos8]
  omega

theorem pos8_row8 (p : Fin 64) : pos8 (row8 p) (col8 p) = p := by
  apply Fin.ext
  simp only [row8, col8, pos8]
  omega

theorem code8V_herm8V (v : Fin 64 → ZMod 2) : code8V (herm8V v) = v := by
  funext p
  obtain ⟨i, j, rfl⟩ : ∃ i j, pos8 i j = p := ⟨_, _, pos8_row8 p⟩
  simp only [code8V, row8_pos8, col8_pos8, herm8V, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [h, ↓reduceIte, lo_mk]
  · simp [lo_mk]
  · simp only [h, lt_asymm h, ↓reduceIte, hi_mk]

theorem isHermM_herm8V (v : Fin 64 → ZMod 2) : IsHermM (herm8V v) := by
  intro i j
  simp only [herm8V, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [h, lt_asymm h, ↓reduceIte]
  · simp [cj_mk_zero]
  · simp only [h, lt_asymm h, ↓reduceIte, cj_cj]

theorem herm8V_code8V {Y : Matrix (Fin 8) (Fin 8) F4} (hY : IsHermM Y) :
    herm8V (code8V Y) = Y := by
  ext i j
  simp only [herm8V, Matrix.of_apply, code8V, row8_pos8, col8_pos8]
  rcases lt_trichotomy i j with h | rfl | h
  · simp only [h, lt_asymm h, ↓reduceIte, mk_lo_hi]
  · simp only [lt_self_iff_false, ↓reduceIte]
    exact mk_lo_of_cj _ (hY i i).symm
  · simp only [h, lt_asymm h, ↓reduceIte, mk_lo_hi]
    exact (hY j i).symm

theorem herm8V_add (v w : Fin 64 → ZMod 2) : herm8V (v + w) = herm8V v + herm8V w := by
  ext i j
  simp only [herm8V, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp [mk_add, mk_add_zero, cj_add]

theorem code8V_add (Y Z : Matrix (Fin 8) (Fin 8) F4) : code8V (Y + Z) = code8V Y + code8V Z := by
  funext p
  simp only [code8V, Matrix.add_apply, Pi.add_apply]
  split_ifs <;> simp [lo_add, hi_add]

@[expose] def herm8 (m : ℕ) : Matrix (Fin 8) (Fin 8) F4 := herm8V (bvec 64 m)

@[expose] def code8 (Y : Matrix (Fin 8) (Fin 8) F4) : ℕ := maskOf 64 (code8V Y)

theorem code8_lt (Y : Matrix (Fin 8) (Fin 8) F4) : code8 Y < 2 ^ 64 := maskOf_lt 64 _

theorem code8_herm8 {m : ℕ} (hm : m < 2 ^ 64) : code8 (herm8 m) = m := by
  rw [code8, herm8, code8V_herm8V, maskOf_bvec hm]

theorem herm8_code8 {Y : Matrix (Fin 8) (Fin 8) F4} (hY : IsHermM Y) : herm8 (code8 Y) = Y := by
  rw [herm8, code8, bvec_maskOf, herm8V_code8V hY]

theorem isHermM_herm8 (m : ℕ) : IsHermM (herm8 m) := isHermM_herm8V _

theorem herm8_xor (a b : ℕ) : herm8 (a ^^^ b) = herm8 a + herm8 b := by
  rw [herm8, bvec_xor, herm8V_add]
  rfl

theorem code8_add (Y Z : Matrix (Fin 8) (Fin 8) F4) : code8 (Y + Z) = code8 Y ^^^ code8 Z := by
  rw [code8, code8V_add, maskOf_add]
  rfl

@[expose] def actH8 (R : Matrix (Fin 8) (Fin 8) F4) (m : ℕ) : ℕ := code8 (R * herm8 m * (barM R)ᵀ)

@[expose] def fld64N (m : ℕ) : ℕ := code8 (barM (herm8 m))

theorem actH8_lt (R : Matrix (Fin 8) (Fin 8) F4) (m : ℕ) : actH8 R m < 2 ^ 64 := code8_lt _

theorem fld64N_lt (m : ℕ) : fld64N m < 2 ^ 64 := code8_lt _

theorem xorLin_actH8 (R : Matrix (Fin 8) (Fin 8) F4) : XorLin (actH8 R) := fun a b => by
  rw [actH8, actH8, actH8, herm8_xor, Matrix.mul_add, Matrix.add_mul, code8_add]

theorem xorLin_fld64N : XorLin fld64N := fun a b => by
  rw [fld64N, fld64N, fld64N, herm8_xor, barM_add, code8_add]

theorem actH8_mul (R R' : Matrix (Fin 8) (Fin 8) F4) (m : ℕ) :
    actH8 (R * R') m = actH8 R (actH8 R' m) := by
  rw [actH8, actH8, actH8, herm8_code8 (isHermM_conj R' (isHermM_herm8 m)), barM_mul,
    transpose_mul]
  simp only [Matrix.mul_assoc]

theorem actH8_one {m : ℕ} (hm : m < 2 ^ 64) : actH8 1 m = m := by
  rw [actH8, barM_one, transpose_one, Matrix.one_mul, Matrix.mul_one, code8_herm8 hm]

theorem fld64N_fld64N {m : ℕ} (hm : m < 2 ^ 64) : fld64N (fld64N m) = m := by
  rw [fld64N, fld64N, herm8_code8 (isHermM_barM (isHermM_herm8 m)), barM_barM, code8_herm8 hm]

theorem fld64N_actH8 (R : Matrix (Fin 8) (Fin 8) F4) (m : ℕ) :
    fld64N (actH8 R m) = actH8 (barM R) (fld64N m) := by
  rw [fld64N, actH8, herm8_code8 (isHermM_conj R (isHermM_herm8 m)), actH8, fld64N,
    herm8_code8 (isHermM_barM (isHermM_herm8 m)), barM_mul, barM_mul, barM_transpose]

@[expose] def coord8 (X : Matrix (Fin 3) (Fin 3) F4) : Fin 8 → F4 :=
  ![X 0 1, X 0 2, X 1 0, X 1 2, X 2 0, X 2 1, X 0 0, X 1 1]

@[expose] def slOf (c : Fin 8 → F4) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of ![![c 6, c 0, c 1], ![c 2, c 7, c 3], ![c 4, c 5, c 6 + c 7]]

theorem coord8_slOf (c : Fin 8 → F4) : coord8 (slOf c) = c := by
  funext k
  fin_cases k <;> rfl

theorem isSl_slOf (c : Fin 8 → F4) : IsSl (slOf c) := rfl

theorem slOf_coord8 {X : Matrix (Fin 3) (Fin 3) F4} (h : IsSl X) : slOf (coord8 X) = X := by
  unfold IsSl at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slOf, coord8, h]

theorem coord8_add (X Y : Matrix (Fin 3) (Fin 3) F4) : coord8 (X + Y) = coord8 X + coord8 Y := by
  funext k
  fin_cases k <;> rfl

theorem coord8_smul (a : F4) (X : Matrix (Fin 3) (Fin 3) F4) :
    coord8 (a • X) = a • coord8 X := by
  funext k
  fin_cases k <;> rfl

@[expose] def coord8L : Matrix (Fin 3) (Fin 3) F4 →+ (Fin 8 → F4) where
  toFun := coord8
  map_zero' := by
    funext k
    fin_cases k <;> rfl
  map_add' := coord8_add

theorem slOf_eq_sum (c : Fin 8 → F4) : slOf c = ∑ l, c l • slOf (Pi.single l 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slOf, Fin.sum_univ_eight, Pi.single_apply]

@[expose] def adM (g h : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 8) (Fin 8) F4 :=
  Matrix.of fun k l => coord8 (g * slOf (Pi.single l 1) * h) k

theorem coord8_conj (g h : Matrix (Fin 3) (Fin 3) F4) (c : Fin 8 → F4) :
    coord8 (g * slOf c * h) = adM g h *ᵥ c := by
  have e : g * slOf c * h = ∑ l, c l • (g * slOf (Pi.single l 1) * h) := by
    rw [slOf_eq_sum c, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  funext k
  have := congrFun (map_sum coord8L (fun l => c l • (g * slOf (Pi.single l 1) * h)) Finset.univ) k
  simp only [coord8L, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  rw [this, Finset.sum_apply]
  simp only [coord8_smul, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, adM, Matrix.of_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem adM_mul {g h g' h' : Matrix (Fin 3) (Fin 3) F4} (hg' : h' * g' = 1) :
    adM (g * g') (h' * h) = adM g h * adM g' h' := by
  ext k l
  have e : g * g' * slOf (Pi.single l 1) * (h' * h) =
      g * slOf (coord8 (g' * slOf (Pi.single l 1) * h')) * h := by
    rw [slOf_coord8 (isSl_conj g' h' hg' (isSl_slOf _))]
    simp only [Matrix.mul_assoc]
  simp only [adM, Matrix.of_apply]
  rw [e, coord8_conj]
  simp only [mulVec, dotProduct, Matrix.mul_apply, adM, Matrix.of_apply]

theorem adM_one : adM 1 1 = 1 := by
  ext k l
  simp only [adM, Matrix.of_apply, Matrix.one_mul, Matrix.mul_one, coord8_slOf, Pi.single_apply,
    Matrix.one_apply]

theorem cj_single (l k : Fin 8) :
    cj ((Pi.single l (1 : F4) : Fin 8 → F4) k) = (Pi.single l (1 : F4) : Fin 8 → F4) k := by
  rw [Pi.single_apply]
  split_ifs
  · exact cj_one
  · exact cj_zero

theorem bar_slOf_single (l : Fin 8) : bar (slOf (Pi.single l 1)) = slOf (Pi.single l 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [bar_apply, slOf, Matrix.of_apply] <;>
    simp [cj_single, cj_add]

theorem coord8_bar (X : Matrix (Fin 3) (Fin 3) F4) (k : Fin 8) :
    coord8 (bar X) k = cj (coord8 X k) := by
  fin_cases k <;> rfl

theorem barM_adM (g h : Matrix (Fin 3) (Fin 3) F4) : barM (adM g h) = adM (bar g) (bar h) := by
  ext k l
  rw [barM_apply, adM, adM, Matrix.of_apply, Matrix.of_apply, ← coord8_bar, bar_mul, bar_mul,
    bar_slOf_single]

@[expose] def gM : Matrix (Fin 8) (Fin 8) F4 :=
  Matrix.of fun k l => coord8 (grSl (slOf (Pi.single l 1))) k

theorem grSl_smul (a : F4) (X : Matrix (Fin 3) (Fin 3) F4) : grSl (a • X) = a • grSl X := by
  ext i j
  simp [grSl]

theorem grSl_sum (f : Fin 8 → Matrix (Fin 3) (Fin 3) F4) : grSl (∑ l, f l) = ∑ l, grSl (f l) := by
  ext i j
  simp [grSl, Matrix.sum_apply]

theorem coord8_grSl (c : Fin 8 → F4) : coord8 (grSl (slOf c)) = gM *ᵥ c := by
  rw [slOf_eq_sum c, grSl_sum]
  funext k
  have := congrFun (map_sum coord8L (fun l => grSl (c l • slOf (Pi.single l 1))) Finset.univ) k
  simp only [coord8L, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
  rw [this, Finset.sum_apply]
  simp only [grSl_smul, coord8_smul, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, gM,
    Matrix.of_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem gM_mul_gM : gM * gM = 1 := by
  ext k l
  have e : (gM * gM) k l = (gM *ᵥ coord8 (grSl (slOf (Pi.single l 1)))) k := by
    simp only [Matrix.mul_apply, mulVec, dotProduct, gM, Matrix.of_apply]
  rw [e, ← coord8_grSl, slOf_coord8 (isSl_grSl (isSl_slOf _)), grSl_grSl, coord8_slOf,
    Pi.single_apply, Matrix.one_apply]

theorem barM_gM : barM gM = gM := by
  ext k l
  rw [barM_apply, gM, Matrix.of_apply, ← coord8_bar, bar_grSl, bar_slOf_single]

theorem gr_conj_eq (g : GL (Fin 3) F4) (X : Matrix (Fin 3) (Fin 3) F4) :
    grM g * X * (w0 * (g : Matrix (Fin 3) (Fin 3) F4)ᵀ * w0) =
      grSl (g * grSl X * (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4)) := by
  rw [grSl_eq, grSl_eq, grM, transpose_mul, transpose_mul, transpose_mul, transpose_mul,
    transpose_transpose, w0_transpose]
  simp only [Matrix.mul_assoc]

theorem adM_grGL (g : GL (Fin 3) F4) :
    adM (grGL g) (↑(grGL g)⁻¹) = gM * adM g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) * gM := by
  ext k l
  rw [grGL_apply, coe_grU, coe_grU_inv]
  simp only [adM, Matrix.of_apply]
  rw [gr_conj_eq, ← slOf_coord8 (isSl_conj _ _ (Units.inv_mul g) (isSl_grSl (isSl_slOf _))),
    coord8_grSl, ← slOf_coord8 (isSl_grSl (isSl_slOf (Pi.single l 1))), coord8_conj,
    coord8_grSl, mulVec_mulVec, mulVec_mulVec]
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, adM]

@[expose] def adGL (g : GL (Fin 3) F4) : Matrix (Fin 8) (Fin 8) F4 :=
  adM g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4)

theorem adGL_mul (g h : GL (Fin 3) F4) : adGL (g * h) = adGL g * adGL h := by
  rw [adGL, adGL, adGL, ← adM_mul (Units.inv_mul h), Units.val_mul, _root_.mul_inv_rev,
    Units.val_mul]

theorem adGL_inv_mul (g : GL (Fin 3) F4) : adGL g⁻¹ * adGL g = 1 := by
  rw [← adGL_mul, inv_mul_cancel, adGL, inv_one, Units.val_one, adM_one]

theorem adGL_mul_inv (g : GL (Fin 3) F4) : adGL g * adGL g⁻¹ = 1 := by
  rw [← adGL_mul, mul_inv_cancel, adGL, inv_one, Units.val_one, adM_one]

theorem actH8_inv_actH8 (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 64) :
    actH8 (adGL g⁻¹) (actH8 (adGL g) m) = m := by
  rw [← actH8_mul, adGL_inv_mul, actH8_one hm]

theorem actH8_actH8_inv (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 64) :
    actH8 (adGL g) (actH8 (adGL g⁻¹) m) = m := by
  rw [← actH8_mul, adGL_mul_inv, actH8_one hm]

theorem ext_toW64 {s t : MulAut (Wn 64)} (h : ∀ m < 2 ^ 64, s (toW 64 m) = t (toW 64 m)) :
    s = t := by
  ext w
  obtain ⟨m, hm, rfl⟩ := toW_surj 64 w
  rw [h m hm]

@[expose] def autU64 (g : GL (Fin 3) F4) : MulAut (Wn 64) :=
  autMask 64 (actH8 (adGL g)) (actH8 (adGL g⁻¹)) (xorLin_actH8 _) (fun _ => code8_lt _)
    (fun _ => code8_lt _) (fun _ hm => actH8_inv_actH8 g hm) (fun _ hm => actH8_actH8_inv g hm)

theorem autU64_toW (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 64) :
    autU64 g (toW 64 m) = toW 64 (actH8 (adGL g) m) :=
  autMask_toW _ _ _ _ _ hm

@[expose] def rho64GL : GL (Fin 3) F4 →* MulAut (Wn 64) where
  toFun := autU64
  map_one' := ext_toW64 fun m hm => by
    show autU64 1 (toW 64 m) = toW 64 m
    rw [autU64_toW _ hm, adGL, inv_one, Units.val_one, adM_one, actH8_one hm]
  map_mul' g h := ext_toW64 fun m hm => by
    show autU64 (g * h) (toW 64 m) = autU64 g (autU64 h (toW 64 m))
    rw [autU64_toW _ hm, autU64_toW _ hm, autU64_toW _ (actH8_lt _ _), adGL_mul, actH8_mul]

theorem rho64GL_toW (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 64) :
    rho64GL g (toW 64 m) = toW 64 (actH8 (adGL g) m) :=
  autU64_toW g hm

@[expose] def fld64 : MulAut (Wn 64) :=
  autMask 64 fld64N fld64N xorLin_fld64N (fun _ => code8_lt _) (fun _ => code8_lt _)
    (fun _ hm => fld64N_fld64N hm) (fun _ hm => fld64N_fld64N hm)

theorem actH8_gM_gM {m : ℕ} (hm : m < 2 ^ 64) : actH8 gM (actH8 gM m) = m := by
  rw [← actH8_mul, gM_mul_gM, actH8_one hm]

@[expose] def gr64 : MulAut (Wn 64) :=
  autMask 64 (actH8 gM) (actH8 gM) (xorLin_actH8 _) (fun _ => code8_lt _) (fun _ => code8_lt _)
    (fun _ hm => actH8_gM_gM hm) (fun _ hm => actH8_gM_gM hm)

theorem fld64_toW {m : ℕ} (hm : m < 2 ^ 64) : fld64 (toW 64 m) = toW 64 (fld64N m) :=
  autMask_toW _ _ _ _ _ hm

theorem gr64_toW {m : ℕ} (hm : m < 2 ^ 64) : gr64 (toW 64 m) = toW 64 (actH8 gM m) :=
  autMask_toW _ _ _ _ _ hm

theorem fld64_sq : fld64 * fld64 = 1 := ext_toW64 fun m hm => by
  rw [MulAut.mul_apply, fld64_toW hm, fld64_toW (fld64N_lt _), fld64N_fld64N hm]
  rfl

theorem gr64_sq : gr64 * gr64 = 1 := ext_toW64 fun m hm => by
  rw [MulAut.mul_apply, gr64_toW hm, gr64_toW (actH8_lt _ _), actH8_gM_gM hm]
  rfl

theorem fld64_gr64 : fld64 * gr64 = gr64 * fld64 := ext_toW64 fun m hm => by
  rw [MulAut.mul_apply, MulAut.mul_apply, gr64_toW hm, fld64_toW (actH8_lt _ _), fld64_toW hm,
    gr64_toW (fld64N_lt _), fld64N_actH8, barM_gM]

theorem fld64_inv : fld64⁻¹ = fld64 := inv_eq_of_mul_eq_one_right fld64_sq

theorem gr64_inv : gr64⁻¹ = gr64 := inv_eq_of_mul_eq_one_right gr64_sq

theorem adGL_frobGL (g : GL (Fin 3) F4) : adGL (frobGL g) = barM (adGL g) := by
  rw [adGL, adGL, coe_frobGL, frobGL_inv, barM_adM]

theorem rho64GL_frobGL (g : GL (Fin 3) F4) :
    rho64GL (frobGL g) = fld64 * rho64GL g * fld64⁻¹ := ext_toW64 fun m hm => by
  rw [fld64_inv, MulAut.mul_apply, MulAut.mul_apply, rho64GL_toW _ hm, fld64_toW hm,
    rho64GL_toW _ (fld64N_lt _), fld64_toW (actH8_lt _ _), fld64N_actH8, fld64N_fld64N hm,
    adGL_frobGL]

theorem rho64GL_grGL (g : GL (Fin 3) F4) :
    rho64GL (grGL g) = gr64 * rho64GL g * gr64⁻¹ := ext_toW64 fun m hm => by
  rw [gr64_inv, MulAut.mul_apply, MulAut.mul_apply, rho64GL_toW _ hm, gr64_toW hm,
    rho64GL_toW _ (actH8_lt _ _), gr64_toW (actH8_lt _ _), ← actH8_mul, ← actH8_mul, adGL,
    adM_grGL]
  rfl

@[expose] def out64 : C22 →* MulAut (Wn 64) := c22Hom fld64 gr64 fld64_sq gr64_sq fld64_gr64

@[expose] def rho64 : Gam →* MulAut (Wn 64) :=
  SemidirectProduct.lift rho64GL out64 fun a => by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [outAct, c22Hom_apply, out64, c22Hom_apply]
    rcases zmod2_cases (Multiplicative.toAdd a).1 with h1 | h1 <;>
      rcases zmod2_cases (Multiplicative.toAdd a).2 with h2 | h2 <;>
      simp only [h1, h2, ite_true, one_ne_zero, ite_false, mul_one, one_mul, inv_one,
        _root_.mul_inv_rev]
    · rw [MulAut.one_apply]
    · exact rho64GL_grGL g
    · exact rho64GL_frobGL g
    · rw [MulAut.mul_apply, rho64GL_frobGL, rho64GL_grGL]
      group

theorem rho64_apply (x : Gam) : rho64 x = rho64GL x.left * out64 x.right := rfl

@[expose] def mulN (a b : ℕ) : ℕ :=
  (a % 2 * (b % 2) + a / 2 * (b / 2)) % 2 +
    2 * ((a % 2 * (b / 2) + a / 2 * (b % 2) + a / 2 * (b / 2)) % 2)

theorem code_mul (x y : F4) : (x * y).code.val = mulN x.code.val y.code.val := by
  obtain ⟨⟨a, ha⟩⟩ := x
  obtain ⟨⟨b, hb⟩⟩ := y
  rw [mk_mul_mk]
  rfl

theorem code_add (x y : F4) : (x + y).code.val = x.code.val ^^^ y.code.val := by
  obtain ⟨⟨a, ha⟩⟩ := x
  obtain ⟨⟨b, hb⟩⟩ := y
  rw [mk_add_mk]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow (n := 2) ha hb)

theorem code_cj (x : F4) : (cj x).code.val = mulN x.code.val x.code.val := code_mul x x

@[expose] def xor8 (f : ℕ → ℕ) : ℕ :=
  f 0 ^^^ f 1 ^^^ f 2 ^^^ f 3 ^^^ f 4 ^^^ f 5 ^^^ f 6 ^^^ f 7

theorem code_sum8 (f : Fin 8 → F4) :
    (∑ l, f l).code.val = xor8 fun l => if h : l < 8 then (f ⟨l, h⟩).code.val else 0 := by
  rw [Fin.sum_univ_eight]
  simp only [code_add, xor8]
  rfl

@[expose] def codes8 (A : Matrix (Fin 8) (Fin 8) F4) : Array ℕ :=
  Array.ofFn (n := 64) fun p => (A (row8 p) (col8 p)).code.val

theorem codes8_getD (A : Matrix (Fin 8) (Fin 8) F4) (i j : Fin 8) :
    (codes8 A).getD (8 * i.val + j.val) 0 = (A i j).code.val := by
  have h : 8 * i.val + j.val < 64 := by omega
  rw [codes8, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [h, ↓reduceDIte, Option.getD_some]
  rw [show (⟨8 * i.val + j.val, h⟩ : Fin 64) = pos8 i j from rfl, row8_pos8, col8_pos8]

@[expose] def Rep8 (Ac : Array ℕ) (A : Matrix (Fin 8) (Fin 8) F4) : Prop :=
  ∀ i j : Fin 8, Ac.getD (8 * i.val + j.val) 0 = (A i j).code.val

theorem rep8_codes8 (A : Matrix (Fin 8) (Fin 8) F4) : Rep8 (codes8 A) A := codes8_getD A

theorem getD_ofFn64 (F : Fin 64 → ℕ) (i j : Fin 8) :
    (Array.ofFn F).getD (8 * i.val + j.val) 0 = F (pos8 i j) := by
  have h : 8 * i.val + j.val < 64 := by omega
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [h, ↓reduceDIte, Option.getD_some]
  rfl

theorem xor8_congr {f g : ℕ → ℕ} (h : ∀ l < 8, f l = g l) : xor8 f = xor8 g := by
  unfold xor8
  rw [h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 (by norm_num), h 5 (by norm_num), h 6 (by norm_num), h 7 (by norm_num)]

@[expose] def mulArr (Ac Bc : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 64) fun p =>
    xor8 fun l => mulN (Ac.getD (8 * (row8 p).val + l) 0) (Bc.getD (8 * l + (col8 p).val) 0)

theorem rep8_mul {Ac Bc : Array ℕ} {A B : Matrix (Fin 8) (Fin 8) F4} (hA : Rep8 Ac A)
    (hB : Rep8 Bc B) : Rep8 (mulArr Ac Bc) (A * B) := by
  intro i k
  rw [mulArr, getD_ofFn64, Matrix.mul_apply, code_sum8, row8_pos8, col8_pos8]
  refine xor8_congr fun l hl => ?_
  rw [dite_eq_left hl, code_mul, ← hA i ⟨l, hl⟩, ← hB ⟨l, hl⟩ k]

@[expose] def bitN (m k : ℕ) : ℕ := if m.testBit k then 1 else 0

@[expose] def ycode (m i j : ℕ) : ℕ :=
  if i < j then bitN m (8 * i + j) + 2 * bitN m (8 * j + i)
  else if j < i then
    mulN (bitN m (8 * j + i) + 2 * bitN m (8 * i + j)) (bitN m (8 * j + i) + 2 * bitN m (8 * i + j))
  else bitN m (8 * i + i)

theorem val_bvec (m : ℕ) (p : Fin 64) : (bvec 64 m p).val = bitN m p := by
  rw [bvec_apply, bitN]
  cases m.testBit p <;> rfl

theorem code_mk (a b : ZMod 2) : (mk a b).code.val = a.val + 2 * b.val := rfl

theorem herm8_code (m : ℕ) (i j : Fin 8) : (herm8 m i j).code.val = ycode m i.val j.val := by
  unfold herm8 herm8V ycode
  rw [Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · have h' : i.val < j.val := h
    simp only [h, h', ↓reduceIte, code_mk, val_bvec]
    rfl
  · simp only [lt_self_iff_false, ↓reduceIte, code_mk, val_bvec, ZMod.val_zero, mul_zero,
      add_zero]
    rfl
  · have h' : j.val < i.val := h
    have h1 : ¬ i < j := lt_asymm h
    have h1' : ¬ i.val < j.val := by omega
    simp only [h, h', h1, h1', ↓reduceIte, code_cj, code_mk, val_bvec]
    rfl

@[expose] def yArr (m : ℕ) : Array ℕ :=
  Array.ofFn (n := 64) fun p => ycode m (row8 p).val (col8 p).val

theorem rep8_herm8 (m : ℕ) : Rep8 (yArr m) (herm8 m) := by
  intro i j
  rw [yArr, getD_ofFn64, row8_pos8, col8_pos8, herm8_code]

@[expose] def starArr (Rc : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 64) fun p =>
    mulN (Rc.getD (8 * (col8 p).val + (row8 p).val) 0) (Rc.getD (8 * (col8 p).val + (row8 p).val) 0)

theorem rep8_star {Rc : Array ℕ} {R : Matrix (Fin 8) (Fin 8) F4} (hR : Rep8 Rc R) :
    Rep8 (starArr Rc) (barM R)ᵀ := by
  intro i j
  rw [starArr, getD_ofFn64, row8_pos8, col8_pos8, transpose_apply, barM_apply, code_cj, hR]

@[expose] def maskArr (Zc : Array ℕ) : ℕ :=
  maskOf 64 fun p =>
    if row8 p < col8 p then ((Zc.getD (8 * (row8 p).val + (col8 p).val) 0 % 2 : ℕ) : ZMod 2)
    else if col8 p < row8 p then ((Zc.getD (8 * (col8 p).val + (row8 p).val) 0 / 2 : ℕ) : ZMod 2)
    else ((Zc.getD (8 * (row8 p).val + (row8 p).val) 0 % 2 : ℕ) : ZMod 2)

theorem maskArr_eq {Zc : Array ℕ} {Z : Matrix (Fin 8) (Fin 8) F4} (hZ : Rep8 Zc Z) :
    maskArr Zc = code8 Z := by
  rw [maskArr, code8]
  congr 1
  funext p
  simp only [code8V, lo, hi]
  rw [hZ, hZ, hZ]

@[expose] def actN64 (Rc : Array ℕ) (m : ℕ) : ℕ :=
  maskArr (mulArr (mulArr Rc (yArr m)) (starArr Rc))

theorem actN64_eq {Rc : Array ℕ} {R : Matrix (Fin 8) (Fin 8) F4} (hR : Rep8 Rc R) (m : ℕ) :
    actN64 Rc m = actH8 R m := by
  rw [actN64, maskArr_eq (rep8_mul (rep8_mul hR (rep8_herm8 m)) (rep8_star hR)), actH8]

@[expose] def fldN64 (m : ℕ) : ℕ :=
  maskArr (Array.ofFn (n := 64) fun p =>
    mulN (ycode m (row8 p).val (col8 p).val) (ycode m (row8 p).val (col8 p).val))

theorem fldN64_eq (m : ℕ) : fldN64 m = fld64N m := by
  rw [fldN64, fld64N]
  refine maskArr_eq fun i j => ?_
  rw [getD_ofFn64, row8_pos8, col8_pos8, barM_apply, code_cj, herm8_code]

@[expose] def colsN64 (Rc : Array ℕ) : List ℕ := (List.range 64).map fun j => actN64 Rc (2 ^ j)

theorem colsN64_eq {Rc : Array ℕ} {R : Matrix (Fin 8) (Fin 8) F4} (hR : Rep8 Rc R) :
    colsN64 Rc = matOf 64 (actH8 R) := by
  simp only [colsN64, matOf, actN64_eq hR]

@[expose] def tabX12_64 : List (List ℕ) :=
  (List.range 4).map fun t => colsN64 (codes8 (adM (um (f4c t) 0 0) (um (f4c t) 0 0)))

@[expose] def tabX13_64 : List (List ℕ) :=
  (List.range 4).map fun t => colsN64 (codes8 (adM (um 0 (f4c t) 0) (um 0 (f4c t) 0)))

@[expose] def tabX23_64 : List (List ℕ) :=
  (List.range 4).map fun t => colsN64 (codes8 (adM (um 0 0 (f4c t)) (um 0 0 (f4c t))))

@[expose] def tabU64 : List (List ℕ) :=
  (List.range 64).map fun u => comp (tabX23_64.getD (u / 16 % 4) [])
    (comp (tabX12_64.getD (u % 4) []) (tabX13_64.getD (u / 4 % 4) []))

@[expose] def fldC64 : List ℕ := (List.range 64).map fun j => fldN64 (2 ^ j)

@[expose] def grC64 : List ℕ := colsN64 (codes8 gM)

@[expose] def idC64 : List ℕ := (List.range 64).map (2 ^ ·)

@[expose] def outC64 (f t : ℕ) : List ℕ :=
  if t = 1 then (if f = 1 then comp fldC64 grC64 else grC64) else (if f = 1 then fldC64 else idC64)

@[expose] def cols64 (p : ℕ) : List ℕ :=
  comp (tabU64.getD (p % 64) []) (outC64 (p / 64 % 2) (p / 128 % 2))

@[expose] def isInvC64 (cs : List ℕ) : Bool :=
  (List.range 64).all (fun i => actM cs (actM cs (2 ^ i)) == 2 ^ i) && !(cs == idC64)

@[expose] def pickWit (n r : ℕ) (cs : List ℕ) : List ℕ :=
  (List.range n).foldl (fun ws i =>
    if ws.length < r && decide (combos ((ws ++ [2 ^ i]).map fun w => actM cs w ^^^ w)).Nodup
    then ws ++ [2 ^ i] else ws) []

@[expose] def dat64 : List (List ℕ × List ℕ) :=
  (((List.range 256).map cols64).filter isInvC64).map fun cs => (cs, pickWit 64 3 cs)

@[expose] def chk64 : Bool := chk1 64 dat64

end CFSG.Quasithin.H13.Ch9.L34M

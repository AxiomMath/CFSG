module

public import CFSG.Quasithin.Vol2.Ch9L34M18

public section

namespace CFSG.Quasithin.H13.Ch9.L34M

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code

theorem toAdd_toW_maskOf {n : ℕ} (w : Wn n) : toW n (maskOf n (Multiplicative.toAdd w)) = w := by
  show Multiplicative.ofAdd (bvec n (maskOf n (Multiplicative.toAdd w))) = w
  rw [bvec_maskOf]
  rfl

theorem maskOf_toW {n m : ℕ} (hm : m < 2 ^ n) : maskOf n (Multiplicative.toAdd (toW n m)) = m :=
  maskOf_bvec hm

@[expose] def autMask (n : ℕ) (f f' : ℕ → ℕ) (hf : XorLin f) (hlt : ∀ m, f m < 2 ^ n)
    (hlt' : ∀ m, f' m < 2 ^ n) (h1 : ∀ m < 2 ^ n, f' (f m) = m)
    (h2 : ∀ m < 2 ^ n, f (f' m) = m) : MulAut (Wn n) where
  toFun w := toW n (f (maskOf n (Multiplicative.toAdd w)))
  invFun w := toW n (f' (maskOf n (Multiplicative.toAdd w)))
  left_inv w := by
    simp only
    rw [maskOf_toW (hlt _), h1 _ (maskOf_lt n _), toAdd_toW_maskOf]
  right_inv w := by
    simp only
    rw [maskOf_toW (hlt' _), h2 _ (maskOf_lt n _), toAdd_toW_maskOf]
  map_mul' w w' := by
    show toW n (f (maskOf n (Multiplicative.toAdd (w * w')))) =
      toW n (f (maskOf n (Multiplicative.toAdd w))) * toW n (f (maskOf n (Multiplicative.toAdd w')))
    rw [toAdd_mul, maskOf_add, hf, toW_xor]

theorem autMask_toW {n : ℕ} {f f' : ℕ → ℕ} (hf : XorLin f) (hlt : ∀ m, f m < 2 ^ n)
    (hlt' : ∀ m, f' m < 2 ^ n) (h1 : ∀ m < 2 ^ n, f' (f m) = m)
    (h2 : ∀ m < 2 ^ n, f (f' m) = m) {m : ℕ} (hm : m < 2 ^ n) :
    autMask n f f' hf hlt hlt' h1 h2 (toW n m) = toW n (f m) := by
  show toW n (f (maskOf n (Multiplicative.toAdd (toW n m)))) = _
  rw [maskOf_toW hm]

@[expose] def slV (v : Fin 16 → ZMod 2) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of ![![mk (v 12) (v 13), mk (v 0) (v 1), mk (v 2) (v 3)],
    ![mk (v 4) (v 5), mk (v 14) (v 15), mk (v 6) (v 7)],
    ![mk (v 8) (v 9), mk (v 10) (v 11), mk (v 12) (v 13) + mk (v 14) (v 15)]]

@[expose] def codeSl (X : Matrix (Fin 3) (Fin 3) F4) : Fin 16 → ZMod 2 :=
  ![lo (X 0 1), hi (X 0 1), lo (X 0 2), hi (X 0 2), lo (X 1 0), hi (X 1 0), lo (X 1 2), hi (X 1 2),
    lo (X 2 0), hi (X 2 0), lo (X 2 1), hi (X 2 1), lo (X 0 0), hi (X 0 0), lo (X 1 1), hi (X 1 1)]

@[expose] def IsSl (X : Matrix (Fin 3) (Fin 3) F4) : Prop := X 2 2 = X 0 0 + X 1 1

theorem codeSl_slV (v : Fin 16 → ZMod 2) : codeSl (slV v) = v := by
  funext i
  fin_cases i <;> simp [codeSl, slV, lo_mk, hi_mk]

theorem isSl_slV (v : Fin 16 → ZMod 2) : IsSl (slV v) := by
  simp [IsSl, slV]

theorem slV_codeSl {X : Matrix (Fin 3) (Fin 3) F4} (h : IsSl X) : slV (codeSl X) = X := by
  unfold IsSl at h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slV, codeSl, mk_lo_hi, h]

theorem slV_add (v w : Fin 16 → ZMod 2) : slV (v + w) = slV v + slV w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slV, mk_add]
  abel

theorem codeSl_add (X Y : Matrix (Fin 3) (Fin 3) F4) : codeSl (X + Y) = codeSl X + codeSl Y := by
  funext i
  fin_cases i <;> simp [codeSl, lo_add, hi_add]

@[expose] def sl (m : ℕ) : Matrix (Fin 3) (Fin 3) F4 := slV (bvec 16 m)

@[expose] def csl (X : Matrix (Fin 3) (Fin 3) F4) : ℕ := maskOf 16 (codeSl X)

theorem csl_lt (X : Matrix (Fin 3) (Fin 3) F4) : csl X < 2 ^ 16 := maskOf_lt 16 _

theorem csl_sl {m : ℕ} (hm : m < 2 ^ 16) : csl (sl m) = m := by
  rw [csl, sl, codeSl_slV, maskOf_bvec hm]

theorem sl_csl {X : Matrix (Fin 3) (Fin 3) F4} (h : IsSl X) : sl (csl X) = X := by
  rw [sl, csl, bvec_maskOf, slV_codeSl h]

theorem isSl_sl (m : ℕ) : IsSl (sl m) := isSl_slV _

theorem sl_xor (a b : ℕ) : sl (a ^^^ b) = sl a + sl b := by
  rw [sl, bvec_xor, slV_add]
  rfl

theorem csl_add (X Y : Matrix (Fin 3) (Fin 3) F4) : csl (X + Y) = csl X ^^^ csl Y := by
  rw [csl, codeSl_add, maskOf_add]
  rfl

theorem isSl_iff_trace (X : Matrix (Fin 3) (Fin 3) F4) : IsSl X ↔ X.trace = 0 := by
  rw [Matrix.trace_fin_three, IsSl]
  constructor
  · intro h
    rw [h]
    exact add_self_F4 _
  · intro h
    calc X 2 2 = X 2 2 + (X 0 0 + X 1 1 + X 2 2) := by rw [h, add_zero]
      _ = X 0 0 + X 1 1 + (X 2 2 + X 2 2) := by abel
      _ = X 0 0 + X 1 1 := by rw [add_self_F4, add_zero]

theorem isSl_conj (g h : Matrix (Fin 3) (Fin 3) F4) (hgh : h * g = 1)
    {X : Matrix (Fin 3) (Fin 3) F4} (hX : IsSl X) : IsSl (g * X * h) := by
  rw [isSl_iff_trace] at hX ⊢
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hgh, Matrix.one_mul]
  exact hX

theorem isSl_bar {X : Matrix (Fin 3) (Fin 3) F4} (h : IsSl X) : IsSl (bar X) := by
  unfold IsSl at h ⊢
  rw [bar_apply, bar_apply, bar_apply, h, cj_add]

@[expose] def grSl (X : Matrix (Fin 3) (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4 :=
  Matrix.of fun i j => X (Fin.rev j) (Fin.rev i)

theorem grSl_eq (X : Matrix (Fin 3) (Fin 3) F4) : grSl X = w0 * Xᵀ * w0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [grSl, w0, Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMul, dotProduct, Fin.rev]

theorem grSl_grSl (X : Matrix (Fin 3) (Fin 3) F4) : grSl (grSl X) = X := by
  ext i j
  simp [grSl, Fin.rev_rev]

theorem grSl_add (X Y : Matrix (Fin 3) (Fin 3) F4) : grSl (X + Y) = grSl X + grSl Y := by
  ext i j
  simp [grSl]

theorem bar_grSl (X : Matrix (Fin 3) (Fin 3) F4) : bar (grSl X) = grSl (bar X) := by
  ext i j
  simp [grSl, bar_apply]

theorem isSl_grSl {X : Matrix (Fin 3) (Fin 3) F4} (h : IsSl X) : IsSl (grSl X) := by
  unfold IsSl at h ⊢
  have e0 : grSl X 0 0 = X 2 2 := rfl
  have e1 : grSl X 1 1 = X 1 1 := rfl
  have e2 : grSl X 2 2 = X 0 0 := rfl
  rw [e0, e1, e2, h, add_assoc, add_self_F4, add_zero]

@[expose] def act16 (g h : Matrix (Fin 3) (Fin 3) F4) (m : ℕ) : ℕ := csl (g * sl m * h)

@[expose] def fld16N (m : ℕ) : ℕ := csl (bar (sl m))

@[expose] def gr16N (m : ℕ) : ℕ := csl (grSl (sl m))

theorem act16_lt (g h : Matrix (Fin 3) (Fin 3) F4) (m : ℕ) : act16 g h m < 2 ^ 16 := csl_lt _

theorem fld16N_lt (m : ℕ) : fld16N m < 2 ^ 16 := csl_lt _

theorem gr16N_lt (m : ℕ) : gr16N m < 2 ^ 16 := csl_lt _

theorem xorLin_act16 (g h : Matrix (Fin 3) (Fin 3) F4) : XorLin (act16 g h) := fun a b => by
  rw [act16, act16, act16, sl_xor, Matrix.mul_add, Matrix.add_mul, csl_add]

theorem xorLin_fld16N : XorLin fld16N := fun a b => by
  rw [fld16N, fld16N, fld16N, sl_xor, bar_add, csl_add]

theorem xorLin_gr16N : XorLin gr16N := fun a b => by
  rw [gr16N, gr16N, gr16N, sl_xor, grSl_add, csl_add]

theorem act16_act16 {g h g' h' : Matrix (Fin 3) (Fin 3) F4} (hgh' : h' * g' = 1) (m : ℕ) :
    act16 g h (act16 g' h' m) = act16 (g * g') (h' * h) m := by
  rw [act16, act16, sl_csl (isSl_conj g' h' hgh' (isSl_sl m)), act16]
  simp only [Matrix.mul_assoc]

theorem act16_one {m : ℕ} (hm : m < 2 ^ 16) : act16 1 1 m = m := by
  rw [act16, Matrix.one_mul, Matrix.mul_one, csl_sl hm]

theorem fld16N_fld16N {m : ℕ} (hm : m < 2 ^ 16) : fld16N (fld16N m) = m := by
  rw [fld16N, fld16N, sl_csl (isSl_bar (isSl_sl m)), bar_bar, csl_sl hm]

theorem gr16N_gr16N {m : ℕ} (hm : m < 2 ^ 16) : gr16N (gr16N m) = m := by
  rw [gr16N, gr16N, sl_csl (isSl_grSl (isSl_sl m)), grSl_grSl, csl_sl hm]

theorem act16_inv_act16 (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 16) :
    act16 (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) g (act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) m) =
      m := by
  rw [act16_act16 (Units.inv_mul g), Units.inv_mul, act16_one hm]

theorem act16_act16_inv (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 16) :
    act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) (act16 (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) g m) =
      m := by
  rw [act16_act16 (Units.mul_inv g), Units.mul_inv, act16_one hm]

@[expose] def autU16 (g : GL (Fin 3) F4) : MulAut (Wn 16) :=
  autMask 16 (act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4))
    (act16 (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) g)
    (xorLin_act16 _ _) (fun _ => csl_lt _) (fun _ => csl_lt _) (fun _ hm => act16_inv_act16 g hm)
    (fun _ hm => act16_act16_inv g hm)

theorem autU16_toW (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 16) :
    autU16 g (toW 16 m) = toW 16 (act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) m) :=
  autMask_toW _ _ _ _ _ hm

theorem ext_toW16 {s t : MulAut (Wn 16)} (h : ∀ m < 2 ^ 16, s (toW 16 m) = t (toW 16 m)) :
    s = t := by
  ext w
  obtain ⟨m, hm, rfl⟩ := toW_surj 16 w
  rw [h m hm]

@[expose] def rho16GL : GL (Fin 3) F4 →* MulAut (Wn 16) where
  toFun := autU16
  map_one' := ext_toW16 fun m hm => by
    show autU16 1 (toW 16 m) = toW 16 m
    rw [autU16_toW _ hm, inv_one, Units.val_one, act16_one hm]
  map_mul' g h := ext_toW16 fun m hm => by
    show autU16 (g * h) (toW 16 m) = autU16 g (autU16 h (toW 16 m))
    rw [autU16_toW _ hm, autU16_toW _ hm, autU16_toW _ (act16_lt _ _ _),
      act16_act16 (Units.inv_mul h), Units.val_mul, _root_.mul_inv_rev, Units.val_mul]

theorem rho16GL_toW (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 2 ^ 16) :
    rho16GL g (toW 16 m) = toW 16 (act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) m) :=
  autU16_toW g hm

@[expose] def fld16 : MulAut (Wn 16) :=
  autMask 16 fld16N fld16N xorLin_fld16N (fun _ => csl_lt _) (fun _ => csl_lt _)
    (fun _ hm => fld16N_fld16N hm) (fun _ hm => fld16N_fld16N hm)

@[expose] def gr16 : MulAut (Wn 16) :=
  autMask 16 gr16N gr16N xorLin_gr16N (fun _ => csl_lt _) (fun _ => csl_lt _)
    (fun _ hm => gr16N_gr16N hm) (fun _ hm => gr16N_gr16N hm)

theorem fld16_toW {m : ℕ} (hm : m < 2 ^ 16) : fld16 (toW 16 m) = toW 16 (fld16N m) :=
  autMask_toW _ _ _ _ _ hm

theorem gr16_toW {m : ℕ} (hm : m < 2 ^ 16) : gr16 (toW 16 m) = toW 16 (gr16N m) :=
  autMask_toW _ _ _ _ _ hm

theorem fld16_sq : fld16 * fld16 = 1 := ext_toW16 fun m hm => by
  rw [MulAut.mul_apply, fld16_toW hm, fld16_toW (fld16N_lt _), fld16N_fld16N hm]
  rfl

theorem gr16_sq : gr16 * gr16 = 1 := ext_toW16 fun m hm => by
  rw [MulAut.mul_apply, gr16_toW hm, gr16_toW (gr16N_lt _), gr16N_gr16N hm]
  rfl

theorem fld16N_gr16N (m : ℕ) : fld16N (gr16N m) = gr16N (fld16N m) := by
  rw [fld16N, gr16N, sl_csl (isSl_grSl (isSl_sl m)), gr16N, fld16N,
    sl_csl (isSl_bar (isSl_sl m)), bar_grSl]

theorem fld16_gr16 : fld16 * gr16 = gr16 * fld16 := ext_toW16 fun m hm => by
  rw [MulAut.mul_apply, MulAut.mul_apply, gr16_toW hm, fld16_toW (gr16N_lt _), fld16_toW hm,
    gr16_toW (fld16N_lt _), fld16N_gr16N]

theorem fld16_inv : fld16⁻¹ = fld16 := inv_eq_of_mul_eq_one_right fld16_sq

theorem gr16_inv : gr16⁻¹ = gr16 := inv_eq_of_mul_eq_one_right gr16_sq

theorem act16_frob (g : GL (Fin 3) F4) (m : ℕ) :
    act16 (bar (g : Matrix (Fin 3) (Fin 3) F4)) (bar (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4)) m =
      fld16N (act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) (fld16N m)) := by
  rw [act16, act16, fld16N, fld16N, sl_csl (isSl_bar (isSl_sl m)),
    sl_csl (isSl_conj _ _ (Units.inv_mul g) (isSl_bar (isSl_sl m))), bar_mul, bar_mul, bar_bar]

theorem act16_gr (g : GL (Fin 3) F4) (m : ℕ) :
    act16 (grM g) (w0 * (g : Matrix (Fin 3) (Fin 3) F4)ᵀ * w0) m =
      gr16N (act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4) (gr16N m)) := by
  rw [act16, act16, gr16N, gr16N, sl_csl (isSl_grSl (isSl_sl m)),
    sl_csl (isSl_conj _ _ (Units.inv_mul g) (isSl_grSl (isSl_sl m))), grSl_eq, grSl_eq, grM,
    transpose_mul, transpose_mul, transpose_mul, transpose_mul, transpose_transpose, w0_transpose]
  simp only [Matrix.mul_assoc]

theorem rho16GL_frobGL (g : GL (Fin 3) F4) :
    rho16GL (frobGL g) = fld16 * rho16GL g * fld16⁻¹ := ext_toW16 fun m hm => by
  rw [fld16_inv, MulAut.mul_apply, MulAut.mul_apply, rho16GL_toW _ hm, fld16_toW hm,
    rho16GL_toW _ (fld16N_lt _), fld16_toW (act16_lt _ _ _), coe_frobGL, frobGL_inv, act16_frob]

theorem rho16GL_grGL (g : GL (Fin 3) F4) :
    rho16GL (grGL g) = gr16 * rho16GL g * gr16⁻¹ := ext_toW16 fun m hm => by
  rw [gr16_inv, MulAut.mul_apply, MulAut.mul_apply, rho16GL_toW _ hm, gr16_toW hm,
    rho16GL_toW _ (gr16N_lt _), gr16_toW (act16_lt _ _ _), grGL_apply, coe_grU, coe_grU_inv,
    act16_gr]

@[expose] def out16 : C22 →* MulAut (Wn 16) := c22Hom fld16 gr16 fld16_sq gr16_sq fld16_gr16

@[expose] def rho16 : Gam →* MulAut (Wn 16) :=
  SemidirectProduct.lift rho16GL out16 fun a => by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [outAct, c22Hom_apply, out16, c22Hom_apply]
    rcases zmod2_cases (Multiplicative.toAdd a).1 with h1 | h1 <;>
      rcases zmod2_cases (Multiplicative.toAdd a).2 with h2 | h2 <;>
      simp only [h1, h2, ite_true, one_ne_zero, ite_false, mul_one, one_mul, inv_one,
        _root_.mul_inv_rev]
    · rw [MulAut.one_apply]
    · exact rho16GL_grGL g
    · exact rho16GL_frobGL g
    · rw [MulAut.mul_apply, rho16GL_frobGL, rho16GL_grGL]
      group

theorem rho16_apply (x : Gam) : rho16 x = rho16GL x.left * out16 x.right := rfl

@[expose] def tabX12 : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768], [1, 2, 4, 8,
    20497, 40994, 68, 136, 1280, 2560, 1024, 2048, 4097, 8194, 16385, 32770], [1, 2, 4, 8, 40979,
    61473, 72, 140, 2304, 3584, 1024, 2048, 4098, 8195, 16386, 32771], [1, 2, 4, 8, 61458, 20515,
    76, 132, 3328, 1536, 1024, 2048, 4099, 8193, 16387, 32769]]

@[expose] def tabX13 : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768], [1, 2, 4, 8, 80,
    160, 64, 128, 4356, 8712, 1025, 2050, 4096, 8192, 16388, 32776], [1, 2, 4, 8, 144, 224, 64, 128,
    8460, 12804, 1026, 2051, 4096, 8192, 16392, 32780], [1, 2, 4, 8, 208, 96, 64, 128, 12552, 4620,
    1027, 2049, 4096, 8192, 16396, 32772]]

@[expose] def tabX23 : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768], [5, 10, 4, 8, 16,
    32, 64, 128, 272, 544, 17472, 34944, 4160, 8320, 16384, 32768], [9, 14, 4, 8, 16, 32, 64, 128,
    288, 560, 33984, 51264, 4224, 8384, 16384, 32768], [13, 6, 4, 8, 16, 32, 64, 128, 304, 528,
    50304, 18624, 4288, 8256, 16384, 32768]]

@[expose] def xchk16 : Bool :=
  decide (tabX12.length = 4) && decide (tabX13.length = 4) && decide (tabX23.length = 4) &&
    ((List.range 4).zip tabX12).all (fun pc =>
      matOf 16 (act16 (um (f4c pc.1) 0 0) (um (f4c pc.1) 0 0)) == pc.2) &&
    ((List.range 4).zip tabX13).all (fun pc =>
      matOf 16 (act16 (um 0 (f4c pc.1) 0) (um 0 (f4c pc.1) 0)) == pc.2) &&
    ((List.range 4).zip tabX23).all (fun pc =>
      matOf 16 (act16 (um 0 0 (f4c pc.1)) (um 0 0 (f4c pc.1))) == pc.2)

theorem xchk16_eq : xchk16 = true := by decide +kernel

@[expose] def tabU16 : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768], [1, 2, 4, 8,
    20497, 40994, 68, 136, 1280, 2560, 1024, 2048, 4097, 8194, 16385, 32770], [1, 2, 4, 8, 40979,
    61473, 72, 140, 2304, 3584, 1024, 2048, 4098, 8195, 16386, 32771], [1, 2, 4, 8, 61458, 20515,
    76, 132, 3328, 1536, 1024, 2048, 4099, 8193, 16387, 32769], [1, 2, 4, 8, 80, 160, 64, 128, 4356,
    8712, 1025, 2050, 4096, 8192, 16388, 32776], [1, 2, 4, 8, 20565, 41130, 68, 136, 5381, 10762,
    1025, 2050, 4097, 8194, 16389, 32778], [1, 2, 4, 8, 41051, 61613, 72, 140, 6406, 11787, 1025,
    2050, 4098, 8195, 16390, 32779], [1, 2, 4, 8, 61534, 20647, 76, 132, 7431, 9737, 1025, 2050,
    4099, 8193, 16391, 32777], [1, 2, 4, 8, 144, 224, 64, 128, 8460, 12804, 1026, 2051, 4096, 8192,
    16392, 32780], [1, 2, 4, 8, 20633, 41198, 68, 136, 9486, 14855, 1026, 2051, 4097, 8194, 16393,
    32782], [1, 2, 4, 8, 41119, 61669, 72, 140, 10511, 15877, 1026, 2051, 4098, 8195, 16394, 32783],
    [1, 2, 4, 8, 61590, 20715, 76, 132, 11533, 13830, 1026, 2051, 4099, 8193, 16395, 32781], [1, 2,
    4, 8, 208, 96, 64, 128, 12552, 4620, 1027, 2049, 4096, 8192, 16396, 32772], [1, 2, 4, 8, 20701,
    41062, 68, 136, 13579, 6669, 1027, 2049, 4097, 8194, 16397, 32774], [1, 2, 4, 8, 41175, 61545,
    72, 140, 14601, 7694, 1027, 2049, 4098, 8195, 16398, 32775], [1, 2, 4, 8, 61658, 20591, 76, 132,
    15626, 5647, 1027, 2049, 4099, 8193, 16399, 32773], [5, 10, 4, 8, 16, 32, 64, 128, 272, 544,
    17472, 34944, 4160, 8320, 16384, 32768], [5, 10, 4, 8, 20565, 41130, 68, 136, 17744, 35488,
    17472, 34944, 4165, 8330, 16389, 32778], [5, 10, 4, 8, 41119, 61669, 72, 140, 35216, 52960,
    17472, 34944, 4170, 8335, 16394, 32783], [5, 10, 4, 8, 61658, 20591, 76, 132, 52688, 18016,
    17472, 34944, 4175, 8325, 16399, 32773], [5, 10, 4, 8, 80, 160, 64, 128, 4436, 8872, 17477,
    34954, 4160, 8320, 16388, 32776], [5, 10, 4, 8, 20497, 40994, 68, 136, 21777, 43554, 17477,
    34954, 4165, 8330, 16385, 32770], [5, 10, 4, 8, 41175, 61545, 72, 140, 39390, 61031, 17477,
    34954, 4170, 8335, 16398, 32775], [5, 10, 4, 8, 61590, 20715, 76, 132, 56731, 26349, 17477,
    34954, 4175, 8325, 16395, 32781], [5, 10, 4, 8, 144, 224, 64, 128, 8604, 13028, 17482, 34959,
    4160, 8320, 16392, 32780], [5, 10, 4, 8, 20701, 41062, 68, 136, 26070, 47723, 17482, 34959,
    4165, 8330, 16397, 32774], [5, 10, 4, 8, 40979, 61473, 72, 140, 43283, 65057, 17482, 34959,
    4170, 8335, 16386, 32771], [5, 10, 4, 8, 61534, 20647, 76, 132, 60761, 30382, 17482, 34959,
    4175, 8325, 16391, 32777], [5, 10, 4, 8, 208, 96, 64, 128, 12760, 4716, 17487, 34949, 4160,
    8320, 16396, 32772], [5, 10, 4, 8, 20633, 41198, 68, 136, 30103, 39657, 17487, 34949, 4165,
    8330, 16393, 32782], [5, 10, 4, 8, 41051, 61613, 72, 140, 47453, 56998, 17487, 34949, 4170,
    8335, 16390, 32779], [5, 10, 4, 8, 61458, 20515, 76, 132, 64786, 22051, 17487, 34949, 4175,
    8325, 16387, 32769], [9, 14, 4, 8, 16, 32, 64, 128, 288, 560, 33984, 51264, 4224, 8384, 16384,
    32768], [9, 14, 4, 8, 20633, 41198, 68, 136, 34272, 51824, 33984, 51264, 4233, 8398, 16393,
    32782], [9, 14, 4, 8, 41175, 61545, 72, 140, 51552, 20144, 33984, 51264, 4238, 8391, 16398,
    32775], [9, 14, 4, 8, 61534, 20647, 76, 132, 19872, 34544, 33984, 51264, 4231, 8393, 16391,
    32777], [9, 14, 4, 8, 80, 160, 64, 128, 4516, 8952, 33993, 51278, 4224, 8384, 16388, 32776], [9,
    14, 4, 8, 20701, 41062, 68, 136, 38253, 60086, 33993, 51278, 4233, 8398, 16397, 32774], [9, 14,
    4, 8, 41119, 61669, 72, 140, 55786, 28287, 33993, 51278, 4238, 8391, 16394, 32783], [9, 14, 4,
    8, 61458, 20515, 76, 132, 23843, 42545, 33993, 51278, 4231, 8393, 16387, 32769], [9, 14, 4, 8,
    144, 224, 64, 128, 8684, 12916, 33998, 51271, 4224, 8384, 16392, 32780], [9, 14, 4, 8, 20497,
    40994, 68, 136, 42274, 64051, 33998, 51271, 4233, 8398, 16385, 32770], [9, 14, 4, 8, 41051,
    61613, 72, 140, 59819, 32509, 33998, 51271, 4238, 8391, 16390, 32779], [9, 14, 4, 8, 61658,
    20591, 76, 132, 28005, 46778, 33998, 51271, 4231, 8393, 16399, 32773], [9, 14, 4, 8, 208, 96,
    64, 128, 12648, 4796, 33991, 51273, 4224, 8384, 16396, 32772], [9, 14, 4, 8, 20565, 41130, 68,
    136, 46511, 56053, 33991, 51273, 4233, 8398, 16389, 32778], [9, 14, 4, 8, 40979, 61473, 72, 140,
    63777, 24114, 33991, 51273, 4238, 8391, 16386, 32771], [9, 14, 4, 8, 61590, 20715, 76, 132,
    32230, 38523, 33991, 51273, 4231, 8393, 16395, 32781], [13, 6, 4, 8, 16, 32, 64, 128, 304, 528,
    50304, 18624, 4288, 8256, 16384, 32768], [13, 6, 4, 8, 20701, 41062, 68, 136, 50608, 19152,
    50304, 18624, 4301, 8262, 16397, 32774], [13, 6, 4, 8, 41051, 61613, 72, 140, 18928, 36432,
    50304, 18624, 4294, 8267, 16390, 32779], [13, 6, 4, 8, 61590, 20715, 76, 132, 36208, 50832,
    50304, 18624, 4299, 8269, 16395, 32781], [13, 6, 4, 8, 80, 160, 64, 128, 4596, 8792, 50317,
    18630, 4288, 8256, 16388, 32776], [13, 6, 4, 8, 20633, 41198, 68, 136, 54649, 27294, 50317,
    18630, 4301, 8262, 16393, 32782], [13, 6, 4, 8, 40979, 61473, 72, 140, 22834, 44563, 50317,
    18630, 4294, 8267, 16386, 32771], [13, 6, 4, 8, 61658, 20591, 76, 132, 40383, 59093, 50317,
    18630, 4299, 8269, 16399, 32773], [13, 6, 4, 8, 144, 224, 64, 128, 8572, 12948, 50310, 18635,
    4288, 8256, 16392, 32780], [13, 6, 4, 8, 20565, 41130, 68, 136, 58874, 31327, 50310, 18635,
    4301, 8262, 16389, 32778], [13, 6, 4, 8, 41175, 61545, 72, 140, 27063, 48857, 50310, 18635,
    4294, 8267, 16398, 32775], [13, 6, 4, 8, 61458, 20515, 76, 132, 44337, 62994, 50310, 18635,
    4299, 8269, 16387, 32769], [13, 6, 4, 8, 208, 96, 64, 128, 12728, 4828, 50315, 18637, 4288,
    8256, 16396, 32772], [13, 6, 4, 8, 20497, 40994, 68, 136, 62771, 23057, 50315, 18637, 4301,
    8262, 16385, 32770], [13, 6, 4, 8, 41119, 61669, 72, 140, 31093, 40602, 50315, 18637, 4294,
    8267, 16394, 32783], [13, 6, 4, 8, 61534, 20647, 76, 132, 48638, 54871, 50315, 18637, 4299,
    8269, 16391, 32777]]

@[expose] def uchk16 : Bool :=
  decide (tabU16.length = 64) &&
    ((List.range 64).zip tabU16).all fun pc => pc.2 == comp (tabX23.getD (pc.1 / 16 % 4) [])
      (comp (tabX12.getD (pc.1 % 4) []) (tabX13.getD (pc.1 / 4 % 4) []))

theorem uchk16_eq : uchk16 = true := by decide +kernel

@[expose] def fldC16 : List ℕ :=
  [1, 3, 4, 12, 16, 48, 64, 192, 256, 768, 1024, 3072, 4096, 12288, 16384, 49152]

@[expose] def grC16 : List ℕ :=
  [64, 128, 4, 8, 1024, 2048, 1, 2, 256, 512, 16, 32, 4096, 8192, 20480, 40960]

@[expose] def idC16 : List ℕ := (List.range 16).map (2 ^ ·)

theorem fldC16_eq : matOf 16 fld16N = fldC16 := by decide +kernel

theorem grC16_eq : matOf 16 gr16N = grC16 := by decide +kernel

@[expose] def outC16 (f t : ℕ) : List ℕ :=
  if t = 1 then (if f = 1 then comp fldC16 grC16 else grC16) else (if f = 1 then fldC16 else idC16)

@[expose] def cols16 (p : ℕ) : List ℕ :=
  comp (tabU16.getD (p % 64) []) (outC16 (p / 64 % 2) (p / 128 % 2))

theorem uGL_decomp (a b c : F4) : uGL a b c = uGL 0 0 c * (uGL a 0 0 * uGL 0 b 0) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_uGL, coe_uGL, coe_uGL, coe_uGL, um_mul, um_mul]
  congr 1 <;> ring

theorem tabU16_spec {u : ℕ} (hu : u < 64) : tabU16.getD u [] = comp (tabX23.getD (u / 16 % 4) [])
    (comp (tabX12.getD (u % 4) []) (tabX13.getD (u / 4 % 4) [])) := by
  have h := uchk16_eq
  simp only [uchk16, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  have := h.2 _ (mem_zip_range h.1 hu)
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact this

theorem xchk16_spec {t : ℕ} (ht : t < 4) :
    matOf 16 (act16 (um (f4c t) 0 0) (um (f4c t) 0 0)) = tabX12.getD t [] ∧
      matOf 16 (act16 (um 0 (f4c t) 0) (um 0 (f4c t) 0)) = tabX13.getD t [] ∧
      matOf 16 (act16 (um 0 0 (f4c t)) (um 0 0 (f4c t))) = tabX23.getD t [] := by
  have h := xchk16_eq
  simp only [xchk16, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by omega)]
  have e4 := h4 _ (mem_zip_range h1 ht)
  have e5 := h5 _ (mem_zip_range h2 ht)
  have e6 := h6 _ (mem_zip_range h3 ht)
  simp only at e4 e5 e6
  exact ⟨e4, e5, e6⟩

theorem std16_vm (m : ℕ) : (MaskCoords.std 16).vm m = toW 16 m := rfl

theorem actsBy_mask {s : MulAut (Wn 16)} {f : ℕ → ℕ} (hf : XorLin f)
    (h : ∀ m < 2 ^ 16, s (toW 16 m) = toW 16 (f m)) :
    ActsBy (MaskCoords.std 16) s (matOf 16 f) := by
  intro m hm
  rw [std16_vm, std16_vm, h m hm, actM_matOf hf 16 m hm]

theorem allLt_matOf (f : ℕ → ℕ) (hf : ∀ m, f m < 2 ^ 16) : AllLt 16 (matOf 16 f) = true := by
  simp only [AllLt, matOf, List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
  exact fun _ _ => hf _

theorem actsBy_fld16 : ActsBy (MaskCoords.std 16) fld16 fldC16 := by
  rw [← fldC16_eq]
  exact actsBy_mask xorLin_fld16N fun _ hm => fld16_toW hm

theorem actsBy_gr16 : ActsBy (MaskCoords.std 16) gr16 grC16 := by
  rw [← grC16_eq]
  exact actsBy_mask xorLin_gr16N fun _ hm => gr16_toW hm

theorem actsBy_one16 : ActsBy (MaskCoords.std 16) 1 idC16 := by
  have h : idC16 = matOf 16 id := rfl
  rw [h]
  exact actsBy_mask (fun _ _ => rfl) fun _ _ => rfl

theorem allLt_fldC16 : AllLt 16 fldC16 = true := by
  rw [← fldC16_eq]
  exact allLt_matOf _ fld16N_lt

theorem allLt_grC16 : AllLt 16 grC16 = true := by
  rw [← grC16_eq]
  exact allLt_matOf _ gr16N_lt

theorem allLt_idC16 : AllLt 16 idC16 = true := by decide

theorem allLt_comp {cs ds : List ℕ} (hcs : AllLt 16 cs = true) :
    AllLt 16 (comp cs ds) = true := by
  simp only [AllLt, comp, List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
  exact fun d _ => actM_lt (allLt_spec hcs) d

theorem actsBy_out16 (f t : ℕ) :
    ActsBy (MaskCoords.std 16) (out16 (Multiplicative.ofAdd (((f % 2 : ℕ) : ZMod 2),
      ((t % 2 : ℕ) : ZMod 2)))) (outC16 (f % 2) (t % 2)) ∧
      AllLt 16 (outC16 (f % 2) (t % 2)) = true := by
  rw [out16, c22Hom_apply, toAdd_ofAdd]
  simp only [ite_cast_zero]
  unfold outC16
  rcases Nat.mod_two_eq_zero_or_one f with hf | hf <;>
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;>
    simp only [hf, ht, ite_true, ite_false, zero_ne_one, mul_one, one_mul]
  · exact ⟨actsBy_one16, allLt_idC16⟩
  · exact ⟨actsBy_gr16, allLt_grC16⟩
  · exact ⟨actsBy_fld16, allLt_fldC16⟩
  · exact ⟨actsBy_mul actsBy_fld16 actsBy_gr16 allLt_grC16, allLt_comp allLt_fldC16⟩

theorem allLt_matOf_act16 (g h : Matrix (Fin 3) (Fin 3) F4) :
    AllLt 16 (matOf 16 (act16 g h)) = true := allLt_matOf _ (act16_lt _ _)

theorem actsBy_rho16GL_matOf (g : GL (Fin 3) F4) :
    ActsBy (MaskCoords.std 16) (rho16GL g)
      (matOf 16 (act16 g (↑g⁻¹ : Matrix (Fin 3) (Fin 3) F4))) :=
  actsBy_mask (xorLin_act16 _ _) fun _ hm => rho16GL_toW g hm

theorem actsBy_x16 {t : ℕ} (ht : t < 4) :
    (ActsBy (MaskCoords.std 16) (rho16GL (uGL (f4c t) 0 0)) (tabX12.getD t []) ∧
      AllLt 16 (tabX12.getD t []) = true) ∧
    (ActsBy (MaskCoords.std 16) (rho16GL (uGL 0 (f4c t) 0)) (tabX13.getD t []) ∧
      AllLt 16 (tabX13.getD t []) = true) ∧
    (ActsBy (MaskCoords.std 16) (rho16GL (uGL 0 0 (f4c t))) (tabX23.getD t []) ∧
      AllLt 16 (tabX23.getD t []) = true) := by
  obtain ⟨h1, h2, h3⟩ := xchk16_spec ht
  have e1 := actsBy_rho16GL_matOf (uGL (f4c t) 0 0)
  have e2 := actsBy_rho16GL_matOf (uGL 0 (f4c t) 0)
  have e3 := actsBy_rho16GL_matOf (uGL 0 0 (f4c t))
  simp only [coe_uGL, coe_uGL_inv, mul_zero, zero_mul, add_zero, zero_add] at e1 e2 e3
  rw [← h1, ← h2, ← h3]
  exact ⟨⟨e1, allLt_matOf_act16 _ _⟩, ⟨e2, allLt_matOf_act16 _ _⟩, ⟨e3, allLt_matOf_act16 _ _⟩⟩

theorem actsBy_uGL16 (p : ℕ) :
    ActsBy (MaskCoords.std 16) (rho16GL (uGL (f4c p) (f4c (p / 4)) (f4c (p / 16))))
      (tabU16.getD (p % 64) []) := by
  have ha := actsBy_x16 (Nat.mod_lt p (show 0 < 4 by norm_num))
  have hb := actsBy_x16 (Nat.mod_lt (p / 4) (show 0 < 4 by norm_num))
  have hc := actsBy_x16 (Nat.mod_lt (p / 16) (show 0 < 4 by norm_num))
  rw [f4c_of_mod (n := p % 4) (x := f4c p) (by unfold f4c; simp only; omega)] at ha
  rw [f4c_of_mod (n := p / 4 % 4) (x := f4c (p / 4)) (by unfold f4c; simp only; omega)] at hb
  rw [f4c_of_mod (n := p / 16 % 4) (x := f4c (p / 16)) (by unfold f4c; simp only; omega)] at hc
  rw [tabU16_spec (Nat.mod_lt _ (by norm_num)), show p % 64 % 4 = p % 4 by omega,
    show p % 64 / 4 % 4 = p / 4 % 4 by omega, show p % 64 / 16 % 4 = p / 16 % 4 by omega,
    uGL_decomp, map_mul, map_mul]
  exact actsBy_mul hc.2.2.1 (actsBy_mul ha.1.1 hb.2.1.1 hb.2.1.2)
    (allLt_comp ha.1.2)

theorem actsBy_cols16 (p : ℕ) : ActsBy (MaskCoords.std 16) (rho16 (sig p)) (cols16 p) := by
  have h := actsBy_out16 (p / 64) (p / 128)
  rw [rho16_apply]
  exact actsBy_mul (actsBy_uGL16 p) h.1 h.2

theorem allLt_cols16 (p : ℕ) : AllLt 16 (cols16 p) = true := by
  refine allLt_comp ?_
  rw [tabU16_spec (Nat.mod_lt _ (by norm_num))]
  exact allLt_comp (actsBy_x16 (Nat.mod_lt _ (by norm_num))).2.2.2

@[expose] def dat16 : List (List ℕ × List ℕ) :=
  [([1, 2, 4, 8, 20497, 40994, 68, 136, 1280, 2560, 1024, 2048, 4097, 8194, 16385, 32770], [16, 32,
    64, 128, 256, 512]), ([1, 2, 4, 8, 40979, 61473, 72, 140, 2304, 3584, 1024, 2048, 4098, 8195,
    16386, 32771], [16, 32, 64, 128, 256, 512]), ([1, 2, 4, 8, 61458, 20515, 76, 132, 3328, 1536,
    1024, 2048, 4099, 8193, 16387, 32769], [16, 32, 64, 128, 256, 512]), ([1, 2, 4, 8, 80, 160, 64,
    128, 4356, 8712, 1025, 2050, 4096, 8192, 16388, 32776], [16, 32, 256, 512, 1024, 2048]), ([1, 2,
    4, 8, 20565, 41130, 68, 136, 5381, 10762, 1025, 2050, 4097, 8194, 16389, 32778], [16, 32, 64,
    128, 256, 512]), ([1, 2, 4, 8, 41051, 61613, 72, 140, 6406, 11787, 1025, 2050, 4098, 8195,
    16390, 32779], [16, 32, 64, 128, 256, 512]), ([1, 2, 4, 8, 61534, 20647, 76, 132, 7431, 9737,
    1025, 2050, 4099, 8193, 16391, 32777], [16, 32, 64, 128, 256, 512]), ([1, 2, 4, 8, 144, 224, 64,
    128, 8460, 12804, 1026, 2051, 4096, 8192, 16392, 32780], [16, 32, 256, 512, 1024, 2048]), ([1,
    2, 4, 8, 20633, 41198, 68, 136, 9486, 14855, 1026, 2051, 4097, 8194, 16393, 32782], [16, 32, 64,
    128, 256, 512]), ([1, 2, 4, 8, 41119, 61669, 72, 140, 10511, 15877, 1026, 2051, 4098, 8195,
    16394, 32783], [16, 32, 64, 128, 256, 512]), ([1, 2, 4, 8, 61590, 20715, 76, 132, 11533, 13830,
    1026, 2051, 4099, 8193, 16395, 32781], [16, 32, 64, 128, 256, 512]), ([1, 2, 4, 8, 208, 96, 64,
    128, 12552, 4620, 1027, 2049, 4096, 8192, 16396, 32772], [16, 32, 256, 512, 1024, 2048]), ([1,
    2, 4, 8, 20701, 41062, 68, 136, 13579, 6669, 1027, 2049, 4097, 8194, 16397, 32774], [16, 32, 64,
    128, 256, 512]), ([1, 2, 4, 8, 41175, 61545, 72, 140, 14601, 7694, 1027, 2049, 4098, 8195,
    16398, 32775], [16, 32, 64, 128, 256, 512]), ([1, 2, 4, 8, 61658, 20591, 76, 132, 15626, 5647,
    1027, 2049, 4099, 8193, 16399, 32773], [16, 32, 64, 128, 256, 512]), ([5, 10, 4, 8, 16, 32, 64,
    128, 272, 544, 17472, 34944, 4160, 8320, 16384, 32768], [1, 2, 256, 512, 1024, 2048]), ([5, 10,
    4, 8, 80, 160, 64, 128, 4436, 8872, 17477, 34954, 4160, 8320, 16388, 32776], [1, 2, 16, 32, 256,
    512]), ([5, 10, 4, 8, 144, 224, 64, 128, 8604, 13028, 17482, 34959, 4160, 8320, 16392, 32780],
    [1, 2, 16, 32, 256, 512]), ([5, 10, 4, 8, 208, 96, 64, 128, 12760, 4716, 17487, 34949, 4160,
    8320, 16396, 32772], [1, 2, 16, 32, 256, 512]), ([9, 14, 4, 8, 16, 32, 64, 128, 288, 560, 33984,
    51264, 4224, 8384, 16384, 32768], [1, 2, 256, 512, 1024, 2048]), ([9, 14, 4, 8, 80, 160, 64,
    128, 4516, 8952, 33993, 51278, 4224, 8384, 16388, 32776], [1, 2, 16, 32, 256, 512]), ([9, 14, 4,
    8, 144, 224, 64, 128, 8684, 12916, 33998, 51271, 4224, 8384, 16392, 32780], [1, 2, 16, 32, 256,
    512]), ([9, 14, 4, 8, 208, 96, 64, 128, 12648, 4796, 33991, 51273, 4224, 8384, 16396, 32772],
    [1, 2, 16, 32, 256, 512]), ([13, 6, 4, 8, 16, 32, 64, 128, 304, 528, 50304, 18624, 4288, 8256,
    16384, 32768], [1, 2, 256, 512, 1024, 2048]), ([13, 6, 4, 8, 80, 160, 64, 128, 4596, 8792,
    50317, 18630, 4288, 8256, 16388, 32776], [1, 2, 16, 32, 256, 512]), ([13, 6, 4, 8, 144, 224, 64,
    128, 8572, 12948, 50310, 18635, 4288, 8256, 16392, 32780], [1, 2, 16, 32, 256, 512]), ([13, 6,
    4, 8, 208, 96, 64, 128, 12728, 4828, 50315, 18637, 4288, 8256, 16396, 32772], [1, 2, 16, 32,
    256, 512]), ([1, 3, 4, 12, 16, 48, 64, 192, 256, 768, 1024, 3072, 4096, 12288, 16384, 49152],
    [2, 8, 32, 128, 512, 2048]), ([1, 3, 4, 12, 20497, 61491, 68, 204, 1280, 3840, 1024, 3072, 4097,
    12291, 16385, 49155], [2, 8, 16, 32, 128, 256]), ([1, 3, 4, 12, 80, 240, 64, 192, 4356, 13068,
    1025, 3075, 4096, 12288, 16388, 49164], [2, 8, 16, 32, 256, 512]), ([1, 3, 4, 12, 20565, 61695,
    68, 204, 5381, 16143, 1025, 3075, 4097, 12291, 16389, 49167], [2, 8, 16, 32, 128, 256]), ([5,
    15, 4, 12, 16, 48, 64, 192, 272, 816, 17472, 52416, 4160, 12480, 16384, 49152], [1, 2, 32, 128,
    512, 1024]), ([5, 15, 4, 12, 80, 240, 64, 192, 4436, 13308, 17477, 52431, 4160, 12480, 16388,
    49164], [1, 2, 16, 32, 256, 512]), ([5, 15, 4, 12, 20701, 61627, 68, 204, 26070, 57277, 17482,
    52421, 4165, 12495, 16397, 49163], [1, 2, 16, 32, 128, 256]), ([5, 15, 4, 12, 20633, 61559, 68,
    204, 30103, 61310, 17487, 52426, 4165, 12495, 16393, 49159], [1, 2, 16, 32, 128, 256]), ([64,
    128, 4, 8, 1024, 2048, 1, 2, 256, 512, 16, 32, 4096, 8192, 20480, 40960], [1, 2, 16, 32, 16384,
    32768]), ([64, 128, 4, 8, 1025, 2050, 1, 2, 4356, 8712, 80, 160, 4096, 8192, 20484, 40968], [1,
    2, 16, 32, 256, 512]), ([64, 128, 4, 8, 1026, 2051, 1, 2, 8460, 12804, 144, 224, 4096, 8192,
    20488, 40972], [1, 2, 16, 32, 256, 512]), ([64, 128, 4, 8, 1027, 2049, 1, 2, 12552, 4620, 208,
    96, 4096, 8192, 20492, 40964], [1, 2, 16, 32, 256, 512]), ([68, 136, 4, 8, 17472, 34944, 5, 10,
    17744, 35488, 20565, 41130, 4165, 8330, 20544, 41088], [1, 2, 16, 32, 1024, 2048]), ([68, 136,
    4, 8, 17477, 34954, 5, 10, 21777, 43554, 20497, 40994, 4165, 8330, 20548, 41096], [1, 2, 16, 32,
    256, 512]), ([68, 136, 4, 8, 17482, 34959, 5, 10, 26070, 47723, 20701, 41062, 4165, 8330, 20552,
    41100], [1, 2, 16, 32, 256, 512]), ([68, 136, 4, 8, 17487, 34949, 5, 10, 30103, 39657, 20633,
    41198, 4165, 8330, 20556, 41092], [1, 2, 16, 32, 256, 512]), ([72, 140, 4, 8, 33984, 51264, 9,
    14, 51552, 20144, 41175, 61545, 4238, 8391, 20608, 41152], [1, 2, 16, 32, 1024, 2048]), ([72,
    140, 4, 8, 33993, 51278, 9, 14, 55786, 28287, 41119, 61669, 4238, 8391, 20612, 41160], [1, 2,
    16, 32, 256, 512]), ([72, 140, 4, 8, 33998, 51271, 9, 14, 59819, 32509, 41051, 61613, 4238,
    8391, 20616, 41164], [1, 2, 16, 32, 256, 512]), ([72, 140, 4, 8, 33991, 51273, 9, 14, 63777,
    24114, 40979, 61473, 4238, 8391, 20620, 41156], [1, 2, 16, 32, 256, 512]), ([76, 132, 4, 8,
    50304, 18624, 13, 6, 36208, 50832, 61590, 20715, 4299, 8269, 20672, 41024], [1, 2, 16, 32, 1024,
    2048]), ([76, 132, 4, 8, 50317, 18630, 13, 6, 40383, 59093, 61658, 20591, 4299, 8269, 20676,
    41032], [1, 2, 16, 32, 256, 512]), ([76, 132, 4, 8, 50310, 18635, 13, 6, 44337, 62994, 61458,
    20515, 4299, 8269, 20680, 41036], [1, 2, 16, 32, 256, 512]), ([76, 132, 4, 8, 50315, 18637, 13,
    6, 48638, 54871, 61534, 20647, 4299, 8269, 20684, 41028], [1, 2, 16, 32, 256, 512]), ([64, 192,
    4, 12, 1024, 3072, 1, 3, 256, 768, 16, 48, 4096, 12288, 20480, 61440], [1, 2, 8, 16, 32, 512]),
    ([64, 192, 4, 12, 1025, 3075, 1, 3, 4356, 13068, 80, 240, 4096, 12288, 20484, 61452], [1, 2, 8,
    16, 32, 256]), ([68, 204, 4, 12, 17472, 52416, 5, 15, 17744, 53232, 20565, 61695, 4165, 12495,
    20544, 61632], [1, 2, 8, 16, 32, 512]), ([68, 204, 4, 12, 17477, 52431, 5, 15, 21777, 65331,
    20497, 61491, 4165, 12495, 20548, 61644], [1, 2, 8, 16, 32, 256]), ([76, 200, 4, 12, 33984,
    19584, 9, 7, 19872, 52048, 61534, 41209, 4231, 12366, 20608, 61504], [1, 2, 8, 16, 32, 512]),
    ([76, 200, 4, 12, 33993, 19591, 9, 7, 23843, 64274, 61458, 41009, 4231, 12366, 20612, 61516],
    [1, 2, 8, 16, 32, 256]), ([72, 196, 4, 12, 50304, 35904, 13, 11, 18928, 51104, 41051, 20726,
    4294, 12429, 20672, 61568], [1, 2, 8, 16, 32, 512]), ([72, 196, 4, 12, 50317, 35915, 13, 11,
    22834, 63265, 40979, 20530, 4294, 12429, 20676, 61580], [1, 2, 8, 16, 32, 256])]

@[expose] def kind16 : List ℕ :=
  [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6,
    1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6,
    1, 1, 6, 6, 1, 1, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6, 6, 6, 1, 6, 6, 6, 1, 6, 6,
    2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
    1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2,
    2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1,
    1, 2, 2, 2, 1, 2, 2, 2, 6, 2, 2, 2, 6, 2, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6, 2, 2, 2, 6, 2, 2,
    2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6, 2, 2, 2, 6, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 6, 2, 2, 2, 6, 2]

@[expose] def pchk16 : Bool :=
  decide (kind16.length = 256) &&
    ((List.range 256).zip kind16).all fun pk =>
      if pk.2 = 0 then pk.1 == 0
      else if pk.2 = 1 then (dat16.map Prod.fst).contains (cols16 pk.1)
      else decide (pk.2 - 2 < 16) &&
        actM (cols16 pk.1) (actM (cols16 pk.1) (2 ^ (pk.2 - 2))) != 2 ^ (pk.2 - 2)

theorem pchk16_eq : pchk16 = true := by decide +kernel

theorem chk2_dat16 : chk2 16 dat16 = true := by decide +kernel

theorem pchk16_spec {p : ℕ} (hp : p < 256) : p = 0 ∨ cols16 p ∈ dat16.map Prod.fst ∨
    ∃ i < 16, actM (cols16 p) (actM (cols16 p) (2 ^ i)) ≠ 2 ^ i := by
  have h := pchk16_eq
  simp only [pchk16, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hk := h.2 _ (mem_zip_range h.1 hp)
  simp only at hk
  split_ifs at hk with h0 h1
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (Or.inl (by simpa using hk))
  · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hk
    exact Or.inr (Or.inr ⟨_, hk.1, hk.2⟩)

theorem cov16 : ∀ s ∈ Sig.map rho16, s * s = 1 → s ≠ 1 →
    ∃ d ∈ dat16, ActsBy (MaskCoords.std 16) s d.1 := by
  rintro _ ⟨x, hx, rfl⟩ hsq h1
  obtain ⟨p, hp, rfl⟩ := exists_sig hx
  rcases pchk16_spec hp with h0 | hm | ⟨i, hi, hne⟩
  · subst h0
    exact absurd (by rw [sig_zero, map_one]) h1
  · obtain ⟨d, hd, hde⟩ := List.mem_map.1 hm
    exact ⟨d, hd, hde ▸ actsBy_cols16 p⟩
  · exfalso
    have hi' : 2 ^ i < 2 ^ 16 := Nat.pow_lt_pow_right (by norm_num) hi
    have hlt := actM_lt (allLt_spec (allLt_cols16 p)) (2 ^ i)
    have h := congrArg (fun f : MulAut (Wn 16) => f (toW 16 (2 ^ i))) hsq
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    have e1 : rho16 (sig p) (toW 16 (2 ^ i)) = toW 16 (actM (cols16 p) (2 ^ i)) :=
      actsBy_cols16 p _ hi'
    have e2 : rho16 (sig p) (toW 16 (actM (cols16 p) (2 ^ i))) =
        toW 16 (actM (cols16 p) (actM (cols16 p) (2 ^ i))) := actsBy_cols16 p _ hlt
    rw [e1, e2] at h
    exact hne (toW_inj (actM_lt (allLt_spec (allLt_cols16 p)) _) hi' h)

theorem cube16 {B : Subgroup (MulAut (Wn 16))} (hB : B ≤ rho16.range) (hB1 : B ≠ ⊥)
    (hsq : ∀ s ∈ B, s * s = 1) (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v) :
    Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ 16 :=
  cube_of_cov2 (MaskCoords.std 16) rho16 sylSig dat16 (by rw [coe_sylSig]; exact cov16)
    chk2_dat16 hB hB1 hsq hq

end CFSG.Quasithin.H13.Ch9.L34M

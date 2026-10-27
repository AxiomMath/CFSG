module

public import CFSG.Quasithin.Vol2.Ch9L34M9
public import Mathlib.Data.LawfulXor.Basic

public section

namespace CFSG.Quasithin.H13.Ch9.L34M

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.Mathieu

abbrev W18 : Type := W9 × W9

theorem xor_div_512 (a b : ℕ) : (a ^^^ b) / 512 = a / 512 ^^^ b / 512 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (512 : ℕ) = 2 ^ 9 by norm_num]
  simp only [Nat.testBit_div_two_pow, Nat.testBit_xor]

theorem add_mul_512_xor {y z y' z' : ℕ} (hy : y < 512) (hy' : y' < 512) :
    (y + 512 * z) ^^^ (y' + 512 * z') = (y ^^^ y') + 512 * (z ^^^ z') := by
  have h9 : (512 : ℕ) = 2 ^ 9 := by norm_num
  rw [h9] at hy hy' ⊢
  rw [add_comm y, add_comm y', add_comm (y ^^^ y')]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hy, Nat.testBit_two_pow_mul_add _ hy',
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hy hy'), Nat.testBit_xor, Nat.testBit_xor]
  split_ifs <;> rfl

theorem toW9_add_mul {y z : ℕ} (hy : y < 512) : toW 9 (y + 512 * z) = toW 9 y := by
  rw [← toW_mod 9 (y + 512 * z), ← toW_mod 9 y]
  congr 1
  rw [show 2 ^ 9 = 512 by norm_num]
  have := hy
  omega

theorem div_add_mul {y z : ℕ} (hy : y < 512) : (y + 512 * z) / 512 = z := by
  have := hy
  omega

theorem xor_eq_add {A B : ℕ} (hA : A < 512) : A ^^^ 512 * B = A + 512 * B := by
  have h := add_mul_512_xor (y := A) (z := 0) (y' := 0) (z' := B) hA (by norm_num)
  simpa using h

@[expose] def coords18 : MaskCoords W18 18 where
  vm m := (toW 9 m, toW 9 (m / 512))
  vm_xor a b := by
    rw [toW_xor, xor_div_512, toW_xor]
    rfl
  vm_mod a := by
    refine Prod.ext ?_ ?_
    · show toW 9 (a % 2 ^ 18) = toW 9 a
      rw [← toW_mod 9 (a % 2 ^ 18), ← toW_mod 9 a]
      congr 1
      omega
    · show toW 9 (a % 2 ^ 18 / 512) = toW 9 (a / 512)
      rw [← toW_mod 9 (a % 2 ^ 18 / 512), ← toW_mod 9 (a / 512)]
      congr 1
      omega
  vm_inj a b ha hb h := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [← toW_mod 9 a, ← toW_mod 9 b] at h1
    have e1 := toW_inj (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
    have e2 := toW_inj (n := 9) (by omega) (by omega) h2
    omega
  vm_surj v := by
    obtain ⟨y, hy, hyv⟩ := toW_surj 9 v.1
    obtain ⟨z, hz, hzv⟩ := toW_surj 9 v.2
    refine ⟨y + 512 * z, by omega, Prod.ext ?_ ?_⟩
    · show toW 9 (y + 512 * z) = v.1
      rw [toW9_add_mul (by omega), hyv]
    · show toW 9 ((y + 512 * z) / 512) = v.2
      rw [div_add_mul (by omega), hzv]

theorem coords18_vm (m : ℕ) : coords18.vm m = (toW 9 m, toW 9 (m / 512)) := rfl

theorem coords18_vm_add {A B : ℕ} (hA : A < 512) :
    coords18.vm (A + 512 * B) = (toW 9 A, toW 9 B) := by
  rw [coords18_vm, toW9_add_mul hA, div_add_mul hA]

@[expose] def rho18GL : GL (Fin 3) F4 →* MulAut W18 where
  toFun g := MulEquiv.prodCongr (rho9 g) (rho9 (grGL g))
  map_one' := by
    simp only [map_one]
    exact MulEquiv.ext fun v => rfl
  map_mul' g h := by
    simp only [map_mul]
    exact MulEquiv.ext fun v => rfl

theorem rho18GL_apply (g : GL (Fin 3) F4) (v : W18) :
    rho18GL g v = (rho9 g v.1, rho9 (grGL g) v.2) := rfl

@[expose] def fld18 : MulAut W18 := MulEquiv.prodCongr fld9 fld9

@[expose] def swap18 : MulAut W18 := MulEquiv.prodComm

theorem fld18_apply (v : W18) : fld18 v = (fld9 v.1, fld9 v.2) := rfl

theorem swap18_apply (v : W18) : swap18 v = (v.2, v.1) := rfl

theorem rho9_grGL_grGL (g : GL (Fin 3) F4) : rho9 (grGL (grGL g)) = rho9 g := by
  rw [show grGL (grGL g) = g from grU_grU g]

theorem fld9_fld9 (w : W9) : fld9 (fld9 w) = w := by
  have h := congrArg (fun f : MulAut W9 => f w) fld9_mul_self
  simpa using h

theorem fld18_sq : fld18 * fld18 = 1 :=
  MulEquiv.ext fun v => Prod.ext (fld9_fld9 v.1) (fld9_fld9 v.2)

theorem swap18_sq : swap18 * swap18 = 1 := MulEquiv.ext fun _ => rfl

theorem fld18_swap18 : fld18 * swap18 = swap18 * fld18 := MulEquiv.ext fun _ => rfl

theorem fld9_inv : fld9⁻¹ = fld9 := inv_eq_of_mul_eq_one_right fld9_mul_self

theorem fld18_inv : fld18⁻¹ = fld18 := inv_eq_of_mul_eq_one_right fld18_sq

theorem swap18_inv : swap18⁻¹ = swap18 := inv_eq_of_mul_eq_one_right swap18_sq

theorem rho18GL_frobGL (g : GL (Fin 3) F4) :
    rho18GL (frobGL g) = fld18 * rho18GL g * fld18⁻¹ := by
  rw [fld18_inv]
  refine MulEquiv.ext fun v => ?_
  simp only [MulAut.mul_apply, rho18GL_apply, fld18_apply]
  rw [rho9_frobGL, ← frobGL_grGL, rho9_frobGL, fld9_inv]
  rfl

theorem rho18GL_grGL (g : GL (Fin 3) F4) :
    rho18GL (grGL g) = swap18 * rho18GL g * swap18⁻¹ := by
  rw [swap18_inv]
  refine MulEquiv.ext fun v => ?_
  simp only [MulAut.mul_apply, rho18GL_apply, swap18_apply]
  rw [rho9_grGL_grGL]

@[expose] def out18 : C22 →* MulAut W18 := c22Hom fld18 swap18 fld18_sq swap18_sq fld18_swap18

@[expose] def rho18 : Gam →* MulAut W18 :=
  SemidirectProduct.lift rho18GL out18 fun a => by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [outAct, c22Hom_apply, out18, c22Hom_apply]
    rcases zmod2_cases (Multiplicative.toAdd a).1 with h1 | h1 <;>
      rcases zmod2_cases (Multiplicative.toAdd a).2 with h2 | h2 <;>
      simp only [h1, h2, ite_true, one_ne_zero, ite_false, mul_one, one_mul, inv_one,
        _root_.mul_inv_rev]
    · rw [MulAut.one_apply]
    · exact rho18GL_grGL g
    · exact rho18GL_frobGL g
    · rw [MulAut.mul_apply, rho18GL_frobGL, rho18GL_grGL]
      group

theorem rho18_apply (x : Gam) : rho18 x = rho18GL x.left * out18 x.right := rfl

@[expose] def sig (p : ℕ) : Gam :=
  ⟨uGL (f4c p) (f4c (p / 4)) (f4c (p / 16)),
    Multiplicative.ofAdd (((p / 64 % 2 : ℕ) : ZMod 2), ((p / 128 % 2 : ℕ) : ZMod 2))⟩

theorem exists_sig {x : Gam} (hx : x ∈ Sig) : ∃ p < 256, x = sig p := by
  obtain ⟨a, b, c, ha⟩ := hx
  have h0 := a.code.isLt
  have h1 := b.code.isLt
  have h2 := c.code.isLt
  have h3 := (Multiplicative.toAdd x.right).1.val_lt
  have h4 := (Multiplicative.toAdd x.right).2.val_lt
  refine ⟨a.code.val + 4 * b.code.val + 16 * c.code.val +
    64 * (Multiplicative.toAdd x.right).1.val + 128 * (Multiplicative.toAdd x.right).2.val,
    by omega, ?_⟩
  apply SemidirectProduct.ext
  · rw [ha, sig]
    show uGL a b c = uGL (f4c _) (f4c _) (f4c _)
    congr 1
    · refine (f4c_code a (b.code.val + 4 * c.code.val +
        16 * (Multiplicative.toAdd x.right).1.val + 32 * (Multiplicative.toAdd x.right).2.val)
        ).symm.trans ?_
      congr 1
      ring
    · refine (f4c_code b (c.code.val + 4 * (Multiplicative.toAdd x.right).1.val +
        8 * (Multiplicative.toAdd x.right).2.val)).symm.trans ?_
      congr 1
      omega
    · refine (f4c_code c ((Multiplicative.toAdd x.right).1.val +
        2 * (Multiplicative.toAdd x.right).2.val)).symm.trans ?_
      congr 1
      omega
  · show x.right = Multiplicative.ofAdd _
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    refine Prod.ext ?_ ?_
    · show (Multiplicative.toAdd x.right).1 = ((_ / 64 % 2 : ℕ) : ZMod 2)
      rw [show (a.code.val + 4 * b.code.val + 16 * c.code.val +
        64 * (Multiplicative.toAdd x.right).1.val + 128 * (Multiplicative.toAdd x.right).2.val) /
          64 % 2 = (Multiplicative.toAdd x.right).1.val by omega, ZMod.natCast_zmod_val]
    · show (Multiplicative.toAdd x.right).2 = ((_ / 128 % 2 : ℕ) : ZMod 2)
      rw [show (a.code.val + 4 * b.code.val + 16 * c.code.val +
        64 * (Multiplicative.toAdd x.right).1.val + 128 * (Multiplicative.toAdd x.right).2.val) /
          128 % 2 = (Multiplicative.toAdd x.right).2.val by omega, ZMod.natCast_zmod_val]

theorem sig_zero : sig 0 = 1 := by
  apply SemidirectProduct.ext
  · apply Units.ext
    show um (f4c 0) (f4c 0) (f4c 0) = 1
    exact um_zero
  · rfl

@[expose] def q1 (p : ℕ) : ℕ := p % 128

@[expose] def q2 (p : ℕ) : ℕ :=
  (f4c (p / 16)).code.val + 4 * (f4c p * f4c (p / 16) + f4c (p / 4)).code.val +
    16 * (f4c p).code.val + 64 * (p / 64 % 2)

theorem q1_lt (p : ℕ) : q1 p < 128 := Nat.mod_lt _ (by norm_num)

theorem q2_lt (p : ℕ) : q2 p < 128 := by
  have h0 := (f4c (p / 16)).code.isLt
  have h1 := (f4c p * f4c (p / 16) + f4c (p / 4)).code.isLt
  have h2 := (f4c p).code.isLt
  have h3 := Nat.mod_lt (p / 64) (show 0 < 2 by norm_num)
  unfold q2
  omega

theorem f4c_of_mod {n : ℕ} {x : F4} (h : n % 4 = x.code.val) : f4c n = x := by
  obtain ⟨⟨k, hk⟩⟩ := x
  unfold f4c
  congr 2

theorem sig9_q1 (p : ℕ) : sig9 (q1 p) = ⟨uGL (f4c p) (f4c (p / 4)) (f4c (p / 16)),
    Multiplicative.ofAdd ((p / 64 % 2 : ℕ) : ZMod 2)⟩ := by
  unfold sig9 q1
  rw [f4c_of_mod (n := p % 128) (x := f4c p) (by unfold f4c; simp only; omega),
    f4c_of_mod (n := p % 128 / 4) (x := f4c (p / 4)) (by unfold f4c; simp only; omega),
    f4c_of_mod (n := p % 128 / 16) (x := f4c (p / 16)) (by unfold f4c; simp only; omega),
    show p % 128 / 64 % 2 = p / 64 % 2 by omega]

theorem sig9_q2 (p : ℕ) : sig9 (q2 p) = ⟨grGL (uGL (f4c p) (f4c (p / 4)) (f4c (p / 16))),
    Multiplicative.ofAdd ((p / 64 % 2 : ℕ) : ZMod 2)⟩ := by
  rw [grGL_uGL]
  have h0 := (f4c (p / 16)).code.isLt
  have h1 := (f4c p * f4c (p / 16) + f4c (p / 4)).code.isLt
  have h2 := (f4c p).code.isLt
  have h3 := Nat.mod_lt (p / 64) (show 0 < 2 by norm_num)
  set n := (f4c (p / 16)).code.val + 4 * (f4c p * f4c (p / 16) + f4c (p / 4)).code.val +
    16 * (f4c p).code.val + 64 * (p / 64 % 2) with hn
  unfold sig9
  rw [show q2 p = n from rfl, f4c_of_mod (n := n) (x := f4c (p / 16)) (by omega),
    f4c_of_mod (n := n / 4) (x := f4c p * f4c (p / 16) + f4c (p / 4)) (by omega),
    f4c_of_mod (n := n / 16) (x := f4c p) (by omega), show n / 64 % 2 = p / 64 % 2 by omega]

theorem rho9G_mk (g : GL (Fin 3) F4) (a : C2) : rho9G ⟨g, a⟩ = rho9 g * fldHom a := rfl

theorem ite_cast_zero {α : Type*} (k : ℕ) (a b : α) :
    (if ((k % 2 : ℕ) : ZMod 2) = 0 then a else b) = if k % 2 = 1 then b else a := by
  by_cases h : k % 2 = 1
  · rw [ite_eq_right (by rw [cast_mod_two_eq_zero]; exact not_not.2 h), ite_eq_left h]
  · rw [ite_eq_left ((cast_mod_two_eq_zero _).2 h), ite_eq_right h]

theorem rho18_sig_apply (p : ℕ) (v : W18) : rho18 (sig p) v =
    if p / 128 % 2 = 1 then (rho9G (sig9 (q1 p)) v.2, rho9G (sig9 (q2 p)) v.1)
    else (rho9G (sig9 (q1 p)) v.1, rho9G (sig9 (q2 p)) v.2) := by
  rw [sig9_q1, sig9_q2, rho9G_mk, rho9G_mk, rho18_apply]
  show rho18GL (uGL (f4c p) (f4c (p / 4)) (f4c (p / 16)))
    (out18 (Multiplicative.ofAdd (((p / 64 % 2 : ℕ) : ZMod 2), ((p / 128 % 2 : ℕ) : ZMod 2))) v) = _
  rw [out18, c22Hom_apply, toAdd_ofAdd, fldHom, c2Hom_apply, toAdd_ofAdd]
  simp only [ite_cast_zero]
  by_cases ht : p / 128 % 2 = 1 <;> by_cases hf : p / 64 % 2 = 1 <;>
    simp only [ht, hf, ite_true, ite_false, MulAut.mul_apply, MulAut.one_apply, rho18GL_apply,
      fld18_apply, swap18_apply, mul_one, one_mul]

theorem actM_append (L₁ L₂ : List ℕ) (m : ℕ) :
    actM (L₁ ++ L₂) m = actM L₁ m ^^^ actM L₂ (m / 2 ^ L₁.length) := by
  induction L₁ generalizing m with
  | nil => simp [actM]
  | cons c L ih =>
    rw [List.cons_append, actM, actM, ih, List.length_cons, Nat.div_div_eq_div_mul, pow_succ,
      mul_comm (2 ^ L.length) 2, Nat.xor_assoc]

theorem mul512_xor (a b : ℕ) : 512 * (a ^^^ b) = 512 * a ^^^ 512 * b := by
  have h := Nat.shiftLeft_xor_distrib (i := 9) (a := a) (b := b)
  simp only [Nat.shiftLeft_eq] at h
  rw [mul_comm, h, mul_comm a, mul_comm b]

theorem actM_map_mul512 (L : List ℕ) (m : ℕ) : actM (L.map (512 * ·)) m = 512 * actM L m := by
  induction L generalizing m with
  | nil => simp [actM]
  | cons c L ih =>
    rw [List.map_cons, actM, actM, ih, mul512_xor]
    split_ifs <;> simp

@[expose] def cols18 (p : ℕ) : List ℕ :=
  if p / 128 % 2 = 1 then (cols9 (q2 p)).map (512 * ·) ++ cols9 (q1 p)
  else cols9 (q1 p) ++ (cols9 (q2 p)).map (512 * ·)

theorem length_cols9 {q : ℕ} (hq : q < 128) : (cols9 q).length = 9 := by
  rw [← tab9_spec hq, length_matOf]

theorem actM_cols9_mod {q : ℕ} (hq : q < 128) (m : ℕ) :
    actM (cols9 q) (m % 512) = actM (cols9 q) m := by
  have h := actM_mod (cols9 q) m
  rwa [length_cols9 hq] at h

theorem actM_cols9_lt {q : ℕ} (hq : q < 128) (m : ℕ) : actM (cols9 q) m < 512 :=
  actM_lt (k := 9) (allLt_spec (allLt_cols9 hq)) m

theorem rho9G_sig9_toW {q : ℕ} (hq : q < 128) (m : ℕ) :
    rho9G (sig9 q) (toW 9 m) = toW 9 (actM (cols9 q) m) := by
  rw [← toW_mod 9 m, ← actM_cols9_mod hq m]
  exact actsBy_cols9 hq _ (Nat.mod_lt _ (by norm_num))

theorem actsBy_cols18 (p : ℕ) : ActsBy coords18 (rho18 (sig p)) (cols18 p) := by
  intro m hm
  have h1 := q1_lt p
  have h2 := q2_lt p
  refine (rho18_sig_apply p _).trans ?_
  rw [coords18_vm, cols18]
  simp only
  split_ifs with ht
  · rw [actM_append, List.length_map, length_cols9 h2, actM_map_mul512, rho9G_sig9_toW h1,
      rho9G_sig9_toW h2, Nat.xor_comm, xor_eq_add (actM_cols9_lt h1 _), coords18_vm_add
      (actM_cols9_lt h1 _)]
    norm_num
  · rw [actM_append, length_cols9 h1, actM_map_mul512, rho9G_sig9_toW h1, rho9G_sig9_toW h2,
      xor_eq_add (actM_cols9_lt h1 _), coords18_vm_add (actM_cols9_lt h1 _)]
    norm_num

theorem allLt_cols18 (p : ℕ) : AllLt 18 (cols18 p) = true := by
  have h1 := allLt_spec (allLt_cols9 (q1_lt p))
  have h2 := allLt_spec (allLt_cols9 (q2_lt p))
  simp only [AllLt, List.all_eq_true, decide_eq_true_eq, cols18]
  intro x hx
  split_ifs at hx <;> simp only [List.mem_append, List.mem_map] at hx
  · rcases hx with ⟨y, hy, rfl⟩ | hx
    · have := h2 y hy; omega
    · have := h1 x hx; omega
  · rcases hx with hx | ⟨y, hy, rfl⟩
    · have := h1 x hx; omega
    · have := h2 y hy; omega

@[expose] def dat18 : List (List ℕ × List ℕ) :=
  [ ([1, 11, 4, 8, 17, 32, 64, 160, 320, 512, 1024, 68608, 4096, 8192, 20480, 40960, 65536, 132096],
    [2, 16, 128]), ([1, 19, 4, 9, 16, 32, 64, 192, 352, 512, 1024, 134144, 4096, 8192, 28672, 36864,
    66560, 131072], [2, 8, 128]), ([1, 27, 4, 9, 17, 32, 64, 224, 288, 512, 1024, 199680, 4096,
    8192, 24576, 45056, 66560, 132096], [2, 8, 128]), ([1, 2, 37, 8, 16, 32, 65, 136, 280, 512,
    1024, 18944, 4096, 8192, 16384, 33280, 69632, 143360], [4, 64, 128]), ([1, 11, 37, 8, 17, 32,
    65, 168, 345, 512, 1024, 89600, 4096, 8192, 20480, 41472, 69632, 144384], [2, 4, 16]), ([1, 19,
    37, 9, 16, 32, 65, 201, 377, 512, 1024, 163328, 4096, 8192, 28672, 37376, 70656, 143360], [2, 4,
    8]), ([1, 27, 37, 9, 17, 32, 65, 233, 312, 512, 1024, 224768, 4096, 8192, 24576, 45568, 70656,
    144384], [2, 4, 8]), ([1, 2, 69, 8, 16, 33, 64, 144, 264, 512, 1024, 35328, 4096, 8192, 16896,
    32768, 73728, 135168], [4, 32, 128]), ([1, 11, 69, 8, 17, 33, 64, 177, 328, 512, 1024, 110080,
    4096, 8192, 20992, 40960, 73728, 136192], [2, 4, 16]), ([1, 19, 69, 9, 16, 33, 64, 208, 361,
    512, 1024, 171520, 4096, 8192, 29184, 36864, 74752, 135168], [2, 4, 8]), ([1, 27, 69, 9, 17, 33,
    64, 241, 297, 512, 1024, 245248, 4096, 8192, 25088, 45056, 74752, 136192], [2, 4, 8]), ([1, 2,
    101, 8, 16, 33, 65, 152, 272, 512, 1024, 51712, 4096, 8192, 16896, 33280, 77824, 139264], [4,
    32, 128]), ([1, 11, 101, 8, 17, 33, 65, 185, 337, 512, 1024, 130560, 4096, 8192, 20992, 41472,
    77824, 140288], [2, 4, 16]), ([1, 19, 101, 9, 16, 33, 65, 217, 368, 512, 1024, 192000, 4096,
    8192, 29184, 37376, 78848, 139264], [2, 4, 8]), ([1, 27, 101, 9, 17, 33, 65, 248, 305, 512,
    1024, 253440, 4096, 8192, 25088, 45568, 78848, 140288], [2, 4, 8]), ([1, 2, 134, 8, 16, 40, 80,
    128, 258, 512, 5632, 2048, 4096, 8704, 16384, 32768, 81920, 163840], [4, 32, 64]), ([1, 2, 175,
    8, 16, 40, 81, 136, 282, 512, 5632, 18944, 4096, 8704, 16384, 33280, 86016, 176640], [4, 32,
    64]), ([1, 2, 215, 8, 16, 41, 80, 144, 266, 512, 5632, 35328, 4096, 8704, 16896, 32768, 90624,
    167936], [4, 32, 64]), ([1, 2, 255, 8, 16, 41, 81, 152, 274, 512, 5632, 51712, 4096, 8704,
    16896, 33280, 94720, 172544], [4, 32, 64]), ([1, 2, 262, 8, 16, 56, 72, 130, 256, 512, 9728,
    2048, 4608, 8192, 16384, 32768, 98304, 180224], [4, 32, 64]), ([1, 2, 319, 8, 16, 56, 73, 138,
    280, 512, 9728, 18944, 4608, 8192, 16384, 33280, 102912, 193024], [4, 32, 64]), ([1, 2, 335, 8,
    16, 57, 72, 146, 264, 512, 9728, 35328, 4608, 8192, 16896, 32768, 106496, 184832], [4, 32, 64]),
    ([1, 2, 375, 8, 16, 57, 73, 154, 272, 512, 9728, 51712, 4608, 8192, 16896, 33280, 111104,
    188416], [4, 32, 64]), ([1, 2, 390, 8, 16, 48, 88, 130, 258, 512, 13824, 2048, 4608, 8704,
    16384, 32768, 114688, 147456], [4, 32, 64]), ([1, 2, 439, 8, 16, 48, 89, 138, 282, 512, 13824,
    18944, 4608, 8704, 16384, 33280, 119296, 159744], [4, 32, 64]), ([1, 2, 479, 8, 16, 49, 88, 146,
    266, 512, 13824, 35328, 4608, 8704, 16896, 32768, 123392, 152064], [4, 32, 64]), ([1, 2, 495, 8,
    16, 49, 89, 154, 274, 512, 13824, 51712, 4608, 8704, 16896, 33280, 126976, 156160], [4, 32,
    64]), ([1, 2, 4, 8, 24, 32, 96, 128, 384, 512, 1024, 2048, 4096, 12288, 16384, 49152, 65536,
    196608], [16, 64, 256]), ([1, 11, 4, 8, 25, 32, 96, 160, 480, 512, 1024, 68608, 4096, 12288,
    20480, 61440, 65536, 197632], [2, 64, 256]), ([1, 2, 37, 8, 24, 32, 97, 136, 400, 512, 1024,
    18944, 4096, 12288, 16384, 49664, 69632, 204800], [4, 16, 256]), ([1, 11, 37, 8, 25, 32, 97,
    168, 497, 512, 1024, 89600, 4096, 12288, 20480, 61952, 69632, 205824], [2, 4, 256]), ([1, 2,
    134, 8, 24, 40, 120, 128, 386, 512, 5632, 2048, 4096, 12800, 16384, 49152, 81920, 245760], [4,
    16, 64]), ([1, 2, 175, 8, 24, 40, 121, 136, 402, 512, 5632, 18944, 4096, 12800, 16384, 49664,
    86016, 254464], [4, 16, 64]), ([1, 11, 215, 8, 25, 41, 121, 185, 483, 512, 5632, 130560, 4096,
    12800, 20992, 61440, 90624, 254976], [2, 4, 64]), ([1, 11, 255, 8, 25, 41, 120, 177, 498, 512,
    5632, 110080, 4096, 12800, 20992, 61952, 94720, 247296], [2, 4, 64]), ([512, 1024, 2048, 4096,
    8192, 16384, 32768, 65536, 131072, 1, 2, 4, 8, 16, 32, 64, 128, 256], [1, 2, 4]), ([512, 1024,
    18944, 4096, 8192, 16384, 33280, 69632, 143360, 1, 2, 37, 8, 16, 32, 65, 136, 280], [1, 2, 4]),
    ([512, 1024, 35328, 4096, 8192, 16896, 32768, 73728, 135168, 1, 2, 69, 8, 16, 33, 64, 144, 264],
    [1, 2, 4]), ([512, 1024, 51712, 4096, 8192, 16896, 33280, 77824, 139264, 1, 2, 101, 8, 16, 33,
    65, 152, 272], [1, 2, 4]), ([512, 5632, 89600, 4096, 8704, 20480, 41472, 81920, 169472, 1, 11,
    134, 8, 17, 40, 80, 168, 338], [1, 2, 4]), ([512, 5632, 68608, 4096, 8704, 20480, 40960, 86016,
    173056, 1, 11, 175, 8, 17, 40, 81, 160, 331], [1, 2, 4]), ([512, 5632, 130560, 4096, 8704,
    20992, 41472, 90624, 165376, 1, 11, 215, 8, 17, 41, 80, 185, 346], [1, 2, 4]), ([512, 5632,
    110080, 4096, 8704, 20992, 40960, 94720, 177152, 1, 11, 255, 8, 17, 41, 81, 177, 323], [1, 2,
    4]), ([512, 9728, 192000, 4608, 8192, 29184, 37376, 108032, 180224, 1, 19, 262, 9, 16, 56, 72,
    202, 368], [1, 2, 4]), ([512, 9728, 171520, 4608, 8192, 29184, 36864, 111616, 193024, 1, 19,
    319, 9, 16, 56, 73, 195, 361], [1, 2, 4]), ([512, 9728, 163328, 4608, 8192, 28672, 37376, 99840,
    184832, 1, 19, 335, 9, 16, 57, 72, 218, 377], [1, 2, 4]), ([512, 9728, 134144, 4608, 8192,
    28672, 36864, 103424, 188416, 1, 19, 375, 9, 16, 57, 73, 211, 352], [1, 2, 4]), ([512, 13824,
    245248, 4608, 8704, 25088, 45056, 128512, 161280, 1, 27, 390, 9, 17, 48, 88, 234, 306], [1, 2,
    4]), ([512, 13824, 253440, 4608, 8704, 25088, 45568, 123904, 148992, 1, 27, 439, 9, 17, 48, 89,
    227, 298], [1, 2, 4]), ([512, 13824, 199680, 4608, 8704, 24576, 45056, 119808, 156672, 1, 27,
    479, 9, 17, 49, 88, 251, 315], [1, 2, 4]), ([512, 13824, 224768, 4608, 8704, 24576, 45568,
    116224, 152576, 1, 27, 495, 9, 17, 49, 89, 242, 291], [1, 2, 4]), ([512, 1024, 2048, 4096,
    12288, 16384, 49152, 65536, 196608, 1, 2, 4, 8, 24, 32, 96, 128, 384], [1, 2, 4]), ([512, 1024,
    18944, 4096, 12288, 16384, 49664, 69632, 204800, 1, 2, 37, 8, 24, 32, 97, 136, 400], [1, 2, 4]),
    ([512, 5632, 89600, 4096, 12800, 20480, 61952, 81920, 251392, 1, 11, 134, 8, 25, 40, 120, 168,
    506], [1, 2, 4]), ([512, 5632, 68608, 4096, 12800, 20480, 61440, 86016, 259072, 1, 11, 175, 8,
    25, 40, 121, 160, 491], [1, 2, 4]), ([512, 9728, 224768, 4608, 12800, 24576, 53760, 108032,
    212992, 1, 27, 262, 9, 24, 56, 112, 242, 458], [1, 2, 4]), ([512, 9728, 199680, 4608, 12800,
    24576, 53248, 111616, 221184, 1, 27, 319, 9, 24, 56, 113, 251, 475], [1, 2, 4]), ([512, 13824,
    163328, 4608, 12288, 28672, 57856, 128512, 243200, 1, 19, 390, 9, 25, 48, 104, 218, 432], [1, 2,
    4]), ([512, 13824, 134144, 4608, 12288, 28672, 57344, 123904, 234496, 1, 19, 439, 9, 25, 48,
    105, 211, 416], [1, 2, 4])]

@[expose] def kind18 : List ℕ :=
  [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4,
    1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4,
    1, 1, 3, 3, 1, 1, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 1, 4, 3, 3, 1, 4, 3, 3, 4, 1, 3, 3, 4, 1, 3, 3,
    4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3,
    1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3,
    3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 1,
    1, 3, 3, 3, 1, 3, 3, 3, 4, 3, 3, 3, 4, 3, 3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 4, 3, 3, 3, 4, 3, 3,
    3, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 4, 3, 3, 3, 4, 3, 3, 1, 3, 3, 3, 1, 3, 3, 3, 4, 3, 3, 3, 4, 3]

@[expose] def pchk18 : Bool :=
  decide (kind18.length = 256) &&
    ((List.range 256).zip kind18).all fun pk =>
      if pk.2 = 0 then pk.1 == 0
      else if pk.2 = 1 then (dat18.map Prod.fst).contains (cols18 pk.1)
      else decide (pk.2 - 2 < 18) &&
        actM (cols18 pk.1) (actM (cols18 pk.1) (2 ^ (pk.2 - 2))) != 2 ^ (pk.2 - 2)

theorem pchk18_eq : pchk18 = true := by decide +kernel

theorem chk1_dat18 : chk1 18 dat18 = true := by decide +kernel

theorem pchk18_spec {p : ℕ} (hp : p < 256) : p = 0 ∨ cols18 p ∈ dat18.map Prod.fst ∨
    ∃ i < 18, actM (cols18 p) (actM (cols18 p) (2 ^ i)) ≠ 2 ^ i := by
  have h := pchk18_eq
  simp only [pchk18, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hk := h.2 _ (mem_zip_range h.1 hp)
  simp only at hk
  split_ifs at hk with h0 h1
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (Or.inl (by simpa using hk))
  · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hk
    exact Or.inr (Or.inr ⟨_, hk.1, hk.2⟩)

theorem cov18 : ∀ s ∈ Sig.map rho18, s * s = 1 → s ≠ 1 →
    ∃ d ∈ dat18, ActsBy coords18 s d.1 := by
  rintro _ ⟨x, hx, rfl⟩ hsq h1
  obtain ⟨p, hp, rfl⟩ := exists_sig hx
  rcases pchk18_spec hp with h0 | hm | ⟨i, hi, hne⟩
  · subst h0
    exact absurd (by rw [sig_zero, map_one]) h1
  · obtain ⟨d, hd, hde⟩ := List.mem_map.1 hm
    exact ⟨d, hd, hde ▸ actsBy_cols18 p⟩
  · exfalso
    have hi' : 2 ^ i < 2 ^ 18 := Nat.pow_lt_pow_right (by norm_num) hi
    have hlt := actM_lt (allLt_spec (allLt_cols18 p)) (2 ^ i)
    have h := congrArg (fun f : MulAut W18 => f (coords18.vm (2 ^ i))) hsq
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    have e1 : rho18 (sig p) (coords18.vm (2 ^ i)) = coords18.vm (actM (cols18 p) (2 ^ i)) :=
      actsBy_cols18 p _ hi'
    have e2 : rho18 (sig p) (coords18.vm (actM (cols18 p) (2 ^ i))) =
        coords18.vm (actM (cols18 p) (actM (cols18 p) (2 ^ i))) := actsBy_cols18 p _ hlt
    rw [e1, e2] at h
    exact hne (coords18.vm_inj _ _ (actM_lt (allLt_spec (allLt_cols18 p)) _) hi' h)

theorem cube18 {B : Subgroup (MulAut W18)} (hB : B ≤ rho18.range) (hB1 : B ≠ ⊥)
    (hsq : ∀ s ∈ B, s * s = 1) (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v) :
    Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ 18 :=
  cube_of_cov1 coords18 rho18 sylSig dat18 (by rw [coe_sylSig]; exact cov18) chk1_dat18 hB hB1
    hsq hq

end CFSG.Quasithin.H13.Ch9.L34M

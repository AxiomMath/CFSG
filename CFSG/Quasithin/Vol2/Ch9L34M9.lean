module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.Quasithin.Vol2.Ch9L34Gam
public import CFSG.Quasithin.Vol2.Ch9L34QBnd

public section

namespace CFSG.Quasithin.H13.Ch9.L34M

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.Mathieu

@[expose] def fldHom : C2 →* MulAut W9 := c2Hom fld9 fld9_mul_self

theorem rho9_frobGL (g : GL (Fin 3) F4) : rho9 (frobGL g) = fld9 * rho9 g * fld9⁻¹ := by
  rw [fld9_mul_rho9, mul_assoc, mul_inv_cancel, mul_one]

@[expose] def rho9G : Gam9 →* MulAut W9 :=
  SemidirectProduct.lift rho9 fldHom fun a => by
    ext g w
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [outAct9, fldHom, c2Hom_apply, c2Hom_apply]
    split_ifs
    · simp
    · rw [rho9_frobGL]
      rfl

theorem rho9G_apply (x : Gam9) : rho9G x = rho9 x.left * fldHom x.right := rfl

@[expose] def f4c (n : ℕ) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def sig9 (p : ℕ) : Gam9 :=
  ⟨uGL (f4c p) (f4c (p / 4)) (f4c (p / 16)), Multiplicative.ofAdd ((p / 64 % 2 : ℕ) : ZMod 2)⟩

theorem f4c_code (x : F4) (m : ℕ) : f4c (x.code.val + 4 * m) = x := by
  obtain ⟨⟨k, hk⟩⟩ := x
  show f4c (k + 4 * m) = ⟨⟨k, hk⟩⟩
  unfold f4c
  congr 2
  omega

theorem exists_sig9 {x : Gam9} (hx : x ∈ Sig9) : ∃ p < 128, x = sig9 p := by
  obtain ⟨a, b, c, ha⟩ := hx
  have h0 := a.code.isLt
  have h1 := b.code.isLt
  have h2 := c.code.isLt
  have h3 := (Multiplicative.toAdd x.right).val_lt
  refine ⟨a.code.val + 4 * b.code.val + 16 * c.code.val + 64 * (Multiplicative.toAdd x.right).val,
    by omega, ?_⟩
  apply SemidirectProduct.ext
  · rw [ha, sig9]
    show uGL a b c = uGL (f4c _) (f4c _) (f4c _)
    congr 1
    · exact (f4c_code a (b.code.val + 4 * c.code.val + 16 * (Multiplicative.toAdd x.right).val)
        |>.symm.trans (by congr 1; ring))
    · refine (f4c_code b (c.code.val + 4 * (Multiplicative.toAdd x.right).val)).symm.trans ?_
      congr 1
      omega
    · refine (f4c_code c (Multiplicative.toAdd x.right).val).symm.trans ?_
      congr 1
      omega
  · show x.right = Multiplicative.ofAdd _
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    have e : (a.code.val + 4 * b.code.val + 16 * c.code.val +
        64 * (Multiplicative.toAdd x.right).val) / 64 % 2 = (Multiplicative.toAdd x.right).val := by
      omega
    rw [e, ZMod.natCast_zmod_val]

theorem sig9_zero : sig9 0 = 1 := by
  apply SemidirectProduct.ext
  · apply Units.ext
    show um (f4c 0) (f4c 0) (f4c 0) = 1
    exact um_zero
  · rfl

@[expose] def actP9 (p m : ℕ) : ℕ :=
  actN (um (f4c p) (f4c (p / 4)) (f4c (p / 16))) (if p / 64 % 2 = 1 then fldN m else m)

theorem xorLin_actP9 (p : ℕ) : XorLin (actP9 p) := by
  intro a b
  unfold actP9
  split_ifs
  · rw [xorLin_fldN, xorLin_actN]
  · rw [xorLin_actN]

theorem rho9_toW (g : GL (Fin 3) F4) {m : ℕ} (hm : m < 512) :
    rho9 g (toW 9 m) = toW 9 (actN g m) := by
  have h := rho9_toW9 g ⟨m, hm⟩
  rw [toW9_apply, toW9_apply] at h
  rw [show toW 9 m = toW 9 ((⟨m, hm⟩ : Fin 512) : ℕ) from rfl, h, ← actN_val]

theorem fld9_toW {m : ℕ} (hm : m < 512) : fld9 (toW 9 m) = toW 9 (fldN m) := by
  have h := fld9_toW9 ⟨m, hm⟩
  rw [toW9_apply, toW9_apply] at h
  rw [show toW 9 m = toW 9 ((⟨m, hm⟩ : Fin 512) : ℕ) from rfl, h, ← fldN_val]

theorem fldN_lt (m : ℕ) : fldN m < 512 := (fld _).isLt

theorem cast_mod_two_eq_zero (k : ℕ) : ((k % 2 : ℕ) : ZMod 2) = 0 ↔ k % 2 ≠ 1 := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> rw [h] <;> decide

theorem rho9G_sig9 (p : ℕ) {m : ℕ} (hm : m < 512) :
    rho9G (sig9 p) (toW 9 m) = toW 9 (actP9 p m) := by
  rw [rho9G_apply, MulAut.mul_apply]
  show rho9 (uGL (f4c p) (f4c (p / 4)) (f4c (p / 16)))
    (fldHom (Multiplicative.ofAdd ((p / 64 % 2 : ℕ) : ZMod 2)) (toW 9 m)) = _
  rw [fldHom, c2Hom_apply, toAdd_ofAdd]
  unfold actP9
  by_cases hf : p / 64 % 2 = 1
  · rw [ite_eq_right (by rw [cast_mod_two_eq_zero]; exact not_not.2 hf), ite_eq_left hf,
      fld9_toW hm, rho9_toW _ (fldN_lt m)]
    rfl
  · rw [ite_eq_left ((cast_mod_two_eq_zero _).2 hf), ite_eq_right hf, MulAut.one_apply,
      rho9_toW _ hm]
    rfl

theorem actsBy_sig9 (p : ℕ) :
    ActsBy (MaskCoords.std 9) (rho9G (sig9 p)) (matOf 9 (actP9 p)) := by
  intro m hm
  show rho9G (sig9 p) (toW 9 m) = toW 9 _
  rw [rho9G_sig9 p hm, actM_matOf (xorLin_actP9 p) 9 m hm]

@[expose] def dat9 : List (List ℕ × List ℕ) :=
  [([1, 11, 4, 8, 17, 32, 64, 160, 320], [2, 16, 128]), ([1, 19, 4, 9, 16, 32, 64, 192, 352], [2, 8,
    128]), ([1, 27, 4, 9, 17, 32, 64, 224, 288], [2, 8, 128]), ([1, 2, 37, 8, 16, 32, 65, 136, 280],
    [4, 64, 128]), ([1, 11, 37, 8, 17, 32, 65, 168, 345], [2, 4, 16]), ([1, 19, 37, 9, 16, 32, 65,
    201, 377], [2, 4, 8]), ([1, 27, 37, 9, 17, 32, 65, 233, 312], [2, 4, 8]), ([1, 2, 69, 8, 16, 33,
    64, 144, 264], [4, 32, 128]), ([1, 11, 69, 8, 17, 33, 64, 177, 328], [2, 4, 16]), ([1, 19, 69,
    9, 16, 33, 64, 208, 361], [2, 4, 8]), ([1, 27, 69, 9, 17, 33, 64, 241, 297], [2, 4, 8]), ([1, 2,
    101, 8, 16, 33, 65, 152, 272], [4, 32, 128]), ([1, 11, 101, 8, 17, 33, 65, 185, 337], [2, 4,
    16]), ([1, 19, 101, 9, 16, 33, 65, 217, 368], [2, 4, 8]), ([1, 27, 101, 9, 17, 33, 65, 248,
    305], [2, 4, 8]), ([1, 2, 134, 8, 16, 40, 80, 128, 258], [4, 32, 64]), ([1, 2, 175, 8, 16, 40,
    81, 136, 282], [4, 32, 64]), ([1, 2, 215, 8, 16, 41, 80, 144, 266], [4, 32, 64]), ([1, 2, 255,
    8, 16, 41, 81, 152, 274], [4, 32, 64]), ([1, 2, 262, 8, 16, 56, 72, 130, 256], [4, 32, 64]),
    ([1, 2, 319, 8, 16, 56, 73, 138, 280], [4, 32, 64]), ([1, 2, 335, 8, 16, 57, 72, 146, 264], [4,
    32, 64]), ([1, 2, 375, 8, 16, 57, 73, 154, 272], [4, 32, 64]), ([1, 2, 390, 8, 16, 48, 88, 130,
    258], [4, 32, 64]), ([1, 2, 439, 8, 16, 48, 89, 138, 282], [4, 32, 64]), ([1, 2, 479, 8, 16, 49,
    88, 146, 266], [4, 32, 64]), ([1, 2, 495, 8, 16, 49, 89, 154, 274], [4, 32, 64]), ([1, 2, 4, 8,
    24, 32, 96, 128, 384], [16, 64, 256]), ([1, 11, 4, 8, 25, 32, 96, 160, 480], [2, 64, 256]), ([1,
    2, 37, 8, 24, 32, 97, 136, 400], [4, 16, 256]), ([1, 11, 37, 8, 25, 32, 97, 168, 497], [2, 4,
    256]), ([1, 2, 134, 8, 24, 40, 120, 128, 386], [4, 16, 64]), ([1, 2, 175, 8, 24, 40, 121, 136,
    402], [4, 16, 64]), ([1, 11, 215, 8, 25, 41, 121, 185, 483], [2, 4, 64]), ([1, 11, 255, 8, 25,
    41, 120, 177, 498], [2, 4, 64])]

@[expose] def tab9 : List (List ℕ) :=
  [[1, 2, 4, 8, 16, 32, 64, 128, 256], [1, 11, 4, 8, 17, 32, 64, 160, 320], [1, 19, 4, 9, 16, 32,
    64, 192, 352], [1, 27, 4, 9, 17, 32, 64, 224, 288], [1, 2, 37, 8, 16, 32, 65, 136, 280], [1, 11,
    37, 8, 17, 32, 65, 168, 345], [1, 19, 37, 9, 16, 32, 65, 201, 377], [1, 27, 37, 9, 17, 32, 65,
    233, 312], [1, 2, 69, 8, 16, 33, 64, 144, 264], [1, 11, 69, 8, 17, 33, 64, 177, 328], [1, 19,
    69, 9, 16, 33, 64, 208, 361], [1, 27, 69, 9, 17, 33, 64, 241, 297], [1, 2, 101, 8, 16, 33, 65,
    152, 272], [1, 11, 101, 8, 17, 33, 65, 185, 337], [1, 19, 101, 9, 16, 33, 65, 217, 368], [1, 27,
    101, 9, 17, 33, 65, 248, 305], [1, 2, 134, 8, 16, 40, 80, 128, 258], [1, 11, 134, 8, 17, 40, 80,
    168, 338], [1, 19, 134, 9, 16, 40, 80, 208, 378], [1, 27, 134, 9, 17, 40, 80, 248, 298], [1, 2,
    175, 8, 16, 40, 81, 136, 282], [1, 11, 175, 8, 17, 40, 81, 160, 331], [1, 19, 175, 9, 16, 40,
    81, 217, 355], [1, 27, 175, 9, 17, 40, 81, 241, 306], [1, 2, 215, 8, 16, 41, 80, 144, 266], [1,
    11, 215, 8, 17, 41, 80, 185, 346], [1, 19, 215, 9, 16, 41, 80, 192, 371], [1, 27, 215, 9, 17,
    41, 80, 233, 291], [1, 2, 255, 8, 16, 41, 81, 152, 274], [1, 11, 255, 8, 17, 41, 81, 177, 323],
    [1, 19, 255, 9, 16, 41, 81, 201, 362], [1, 27, 255, 9, 17, 41, 81, 224, 315], [1, 2, 262, 8, 16,
    56, 72, 130, 256], [1, 11, 262, 8, 17, 56, 72, 186, 328], [1, 19, 262, 9, 16, 56, 72, 202, 368],
    [1, 27, 262, 9, 17, 56, 72, 242, 312], [1, 2, 319, 8, 16, 56, 73, 138, 280], [1, 11, 319, 8, 17,
    56, 73, 178, 337], [1, 19, 319, 9, 16, 56, 73, 195, 361], [1, 27, 319, 9, 17, 56, 73, 251, 288],
    [1, 2, 335, 8, 16, 57, 72, 146, 264], [1, 11, 335, 8, 17, 57, 72, 171, 320], [1, 19, 335, 9, 16,
    57, 72, 218, 377], [1, 27, 335, 9, 17, 57, 72, 227, 305], [1, 2, 375, 8, 16, 57, 73, 154, 272],
    [1, 11, 375, 8, 17, 57, 73, 163, 345], [1, 19, 375, 9, 16, 57, 73, 211, 352], [1, 27, 375, 9,
    17, 57, 73, 234, 297], [1, 2, 390, 8, 16, 48, 88, 130, 258], [1, 11, 390, 8, 17, 48, 88, 178,
    346], [1, 19, 390, 9, 16, 48, 88, 218, 362], [1, 27, 390, 9, 17, 48, 88, 234, 306], [1, 2, 439,
    8, 16, 48, 89, 138, 282], [1, 11, 439, 8, 17, 48, 89, 186, 323], [1, 19, 439, 9, 16, 48, 89,
    211, 371], [1, 27, 439, 9, 17, 48, 89, 227, 298], [1, 2, 479, 8, 16, 49, 88, 146, 266], [1, 11,
    479, 8, 17, 49, 88, 163, 338], [1, 19, 479, 9, 16, 49, 88, 202, 355], [1, 27, 479, 9, 17, 49,
    88, 251, 315], [1, 2, 495, 8, 16, 49, 89, 154, 274], [1, 11, 495, 8, 17, 49, 89, 171, 331], [1,
    19, 495, 9, 16, 49, 89, 195, 378], [1, 27, 495, 9, 17, 49, 89, 242, 291], [1, 2, 4, 8, 24, 32,
    96, 128, 384], [1, 11, 4, 8, 25, 32, 96, 160, 480], [1, 19, 4, 9, 25, 32, 96, 192, 416], [1, 27,
    4, 9, 24, 32, 96, 224, 448], [1, 2, 37, 8, 24, 32, 97, 136, 400], [1, 11, 37, 8, 25, 32, 97,
    168, 497], [1, 19, 37, 9, 25, 32, 97, 201, 432], [1, 27, 37, 9, 24, 32, 97, 233, 465], [1, 2,
    69, 8, 24, 33, 97, 144, 408], [1, 11, 69, 8, 25, 33, 97, 177, 505], [1, 19, 69, 9, 25, 33, 97,
    208, 441], [1, 27, 69, 9, 24, 33, 97, 241, 472], [1, 2, 101, 8, 24, 33, 96, 152, 392], [1, 11,
    101, 8, 25, 33, 96, 185, 488], [1, 19, 101, 9, 25, 33, 96, 217, 425], [1, 27, 101, 9, 24, 33,
    96, 248, 457], [1, 2, 134, 8, 24, 40, 120, 128, 386], [1, 11, 134, 8, 25, 40, 120, 168, 506],
    [1, 19, 134, 9, 25, 40, 120, 208, 426], [1, 27, 134, 9, 24, 40, 120, 248, 466], [1, 2, 175, 8,
    24, 40, 121, 136, 402], [1, 11, 175, 8, 25, 40, 121, 160, 491], [1, 19, 175, 9, 25, 40, 121,
    217, 442], [1, 27, 175, 9, 24, 40, 121, 241, 451], [1, 2, 215, 8, 24, 41, 121, 144, 410], [1,
    11, 215, 8, 25, 41, 121, 185, 483], [1, 19, 215, 9, 25, 41, 121, 192, 435], [1, 27, 215, 9, 24,
    41, 121, 233, 458], [1, 2, 255, 8, 24, 41, 120, 152, 394], [1, 11, 255, 8, 25, 41, 120, 177,
    498], [1, 19, 255, 9, 25, 41, 120, 201, 419], [1, 27, 255, 9, 24, 41, 120, 224, 475], [1, 2,
    262, 8, 24, 56, 112, 130, 386], [1, 11, 262, 8, 25, 56, 112, 186, 498], [1, 19, 262, 9, 25, 56,
    112, 202, 442], [1, 27, 262, 9, 24, 56, 112, 242, 458], [1, 2, 319, 8, 24, 56, 113, 138, 402],
    [1, 11, 319, 8, 25, 56, 113, 178, 483], [1, 19, 319, 9, 25, 56, 113, 195, 426], [1, 27, 319, 9,
    24, 56, 113, 251, 475], [1, 2, 335, 8, 24, 57, 113, 146, 410], [1, 11, 335, 8, 25, 57, 113, 171,
    491], [1, 19, 335, 9, 25, 57, 113, 218, 419], [1, 27, 335, 9, 24, 57, 113, 227, 466], [1, 2,
    375, 8, 24, 57, 112, 154, 394], [1, 11, 375, 8, 25, 57, 112, 163, 506], [1, 19, 375, 9, 25, 57,
    112, 211, 435], [1, 27, 375, 9, 24, 57, 112, 234, 451], [1, 2, 390, 8, 24, 48, 104, 130, 384],
    [1, 11, 390, 8, 25, 48, 104, 178, 488], [1, 19, 390, 9, 25, 48, 104, 218, 432], [1, 27, 390, 9,
    24, 48, 104, 234, 472], [1, 2, 439, 8, 24, 48, 105, 138, 400], [1, 11, 439, 8, 25, 48, 105, 186,
    505], [1, 19, 439, 9, 25, 48, 105, 211, 416], [1, 27, 439, 9, 24, 48, 105, 227, 457], [1, 2,
    479, 8, 24, 49, 105, 146, 408], [1, 11, 479, 8, 25, 49, 105, 163, 497], [1, 19, 479, 9, 25, 49,
    105, 202, 425], [1, 27, 479, 9, 24, 49, 105, 251, 448], [1, 2, 495, 8, 24, 49, 104, 154, 392],
    [1, 11, 495, 8, 25, 49, 104, 171, 480], [1, 19, 495, 9, 25, 49, 104, 195, 441], [1, 27, 495, 9,
    24, 49, 104, 242, 465]]

@[expose] def tchk9 : Bool :=
  decide (tab9.length = 128) &&
    ((List.range 128).zip tab9).all fun pc => matOf 9 (actP9 pc.1) == pc.2

theorem tchk9_eq : tchk9 = true := by decide +kernel

@[expose] def cols9 (p : ℕ) : List ℕ := tab9.getD p []

theorem mem_zip_range {α : Type*} {l : List α} {N : ℕ} (hl : l.length = N) {p : ℕ}
    (hp : p < N) : (p, l[p]'(by omega)) ∈ (List.range N).zip l := by
  rw [List.mem_iff_getElem]
  refine ⟨p, by simp [hl, hp], ?_⟩
  simp [List.getElem_zip, List.getElem_range]

theorem tab9_spec {p : ℕ} (hp : p < 128) : matOf 9 (actP9 p) = cols9 p := by
  have h := tchk9_eq
  simp only [tchk9, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  have := h.2 _ (mem_zip_range h.1 hp)
  rw [cols9, List.getD_eq_getElem _ _ (by omega)]
  exact this

@[expose] def kind9 : List ℕ :=
  [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4,
    1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4, 1, 4, 4, 4,
    1, 1, 3, 3, 1, 1, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 1, 4, 3, 3, 1, 4, 3, 3, 4, 1, 3, 3, 4, 1, 3, 3,
    4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3, 4, 4, 3, 3]

@[expose] def pchk9 : Bool :=
  decide (kind9.length = 128) &&
    ((List.range 128).zip kind9).all fun pk =>
      if pk.2 = 0 then pk.1 == 0
      else if pk.2 = 1 then (dat9.map Prod.fst).contains (cols9 pk.1)
      else decide (pk.2 - 2 < 9) &&
        actM (cols9 pk.1) (actM (cols9 pk.1) (2 ^ (pk.2 - 2))) != 2 ^ (pk.2 - 2)

theorem pchk9_eq : pchk9 = true := by decide +kernel

theorem chk1_dat9 : chk1 9 dat9 = true := by decide +kernel

theorem pchk9_spec {p : ℕ} (hp : p < 128) : p = 0 ∨ cols9 p ∈ dat9.map Prod.fst ∨
    ∃ i < 9, actM (cols9 p) (actM (cols9 p) (2 ^ i)) ≠ 2 ^ i := by
  have h := pchk9_eq
  simp only [pchk9, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  have hk := h.2 _ (mem_zip_range h.1 hp)
  simp only at hk
  split_ifs at hk with h0 h1
  · exact Or.inl (by simpa using hk)
  · exact Or.inr (Or.inl (by simpa using hk))
  · simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hk
    exact Or.inr (Or.inr ⟨_, hk.1, hk.2⟩)

theorem actP9_lt (p m : ℕ) : actP9 p m < 512 := (act _ _).isLt

theorem actsBy_cols9 {p : ℕ} (hp : p < 128) :
    ActsBy (MaskCoords.std 9) (rho9G (sig9 p)) (cols9 p) := by
  rw [← tab9_spec hp]
  exact actsBy_sig9 p

theorem allLt_cols9 {p : ℕ} (hp : p < 128) : AllLt 9 (cols9 p) = true := by
  rw [← tab9_spec hp]
  simp only [AllLt, matOf, List.all_map, List.all_eq_true, Function.comp_apply,
    decide_eq_true_eq]
  intro j _
  exact actP9_lt p _

theorem cov9 : ∀ s ∈ Sig9.map rho9G, s * s = 1 → s ≠ 1 →
    ∃ d ∈ dat9, ActsBy (MaskCoords.std 9) s d.1 := by
  rintro _ ⟨x, hx, rfl⟩ hsq h1
  obtain ⟨p, hp, rfl⟩ := exists_sig9 hx
  rcases pchk9_spec hp with h0 | hm | ⟨i, hi, hne⟩
  · subst h0
    exact absurd (by rw [sig9_zero, map_one]) h1
  · obtain ⟨d, hd, hde⟩ := List.mem_map.1 hm
    exact ⟨d, hd, hde ▸ actsBy_cols9 hp⟩
  · exfalso
    have hi' : 2 ^ i < 2 ^ 9 := Nat.pow_lt_pow_right (by norm_num) hi
    have hlt := actM_lt (allLt_spec (allLt_cols9 hp)) (2 ^ i)
    have h := congrArg (fun f : MulAut W9 => f (toW 9 (2 ^ i))) hsq
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    rw [show toW 9 (2 ^ i) = (MaskCoords.std 9).vm (2 ^ i) from rfl, actsBy_cols9 hp _ hi',
      actsBy_cols9 hp _ hlt] at h
    exact hne ((MaskCoords.std 9).vm_inj _ _ (actM_lt (allLt_spec (allLt_cols9 hp)) _) hi' h)

theorem card_fixV_map_conj {V : Type*} [CommGroup V] (c : MulAut V) (B : Subgroup (MulAut V)) :
    Nat.card (fixV (B.map (MulAut.conj c).toMonoidHom)) = Nat.card (fixV B) :=
  CFSG.Quasithin.ConjTransport.card_fixV_map_conj B c

theorem conj_mul_self {G : Type*} [Group G] (c x : G) (hx : x * x = 1) :
    MulAut.conj c x * MulAut.conj c x = 1 := by
  rw [← map_mul, hx, map_one]

theorem quad_map_conj {V : Type*} [CommGroup V] (c : MulAut V) {B : Subgroup (MulAut V)}
    (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v) :
    ∀ s ∈ B.map (MulAut.conj c).toMonoidHom, ∀ t ∈ B.map (MulAut.conj c).toMonoidHom, ∀ v,
      s (t v * v) = t v * v := by
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ v
  have h := hq s hs t ht (c⁻¹ v)
  show (c * s * c⁻¹) ((c * t * c⁻¹) v * v) = (c * t * c⁻¹) v * v
  simp only [MulAut.mul_apply]
  rw [map_mul c⁻¹, MulAut.inv_apply_self, h, map_mul, MulAut.apply_inv_self]

theorem cube_of_cov1 {Γ V : Type*} [Group Γ] [Finite Γ] [CommGroup V] {n : ℕ}
    (c : MaskCoords V n) (ρ : Γ →* MulAut V) (P₀ : Sylow 2 Γ) (dat : List (List ℕ × List ℕ))
    (hcov : ∀ s ∈ (P₀ : Subgroup Γ).map ρ, s * s = 1 → s ≠ 1 → ∃ d ∈ dat, ActsBy c s d.1)
    (hchk : chk1 n dat = true) {B : Subgroup (MulAut V)} (hB : B ≤ ρ.range) (hB1 : B ≠ ⊥)
    (hsq : ∀ s ∈ B, s * s = 1) (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v) :
    Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ n := by
  have h2 : IsPGroup 2 B := fun x => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hsq x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le ρ P₀ hB h2
  set e := (ρ g)⁻¹ with he
  have key := cube_bound_one (c := c) (B := B.map (MulAut.conj e).toMonoidHom) hg
    (fun h => hB1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj e).injective).1 h))
    (by rintro _ ⟨s, hs, rfl⟩; exact conj_mul_self e s (hsq s hs)) (quad_map_conj e hq)
    dat hcov hchk
  rw [Subgroup.card_map_of_injective (MulAut.conj e).injective] at key
  calc Nat.card B ^ 3 * Nat.card (fixV B) =
      Nat.card B ^ 3 * Nat.card (fixV (B.map (MulAut.conj e).toMonoidHom)) := by
        congr 1
        exact (card_fixV_map_conj e B).symm
    _ ≤ 2 ^ n := key

theorem cube_of_cov2 {Γ V : Type*} [Group Γ] [Finite Γ] [CommGroup V] {n : ℕ}
    (c : MaskCoords V n) (ρ : Γ →* MulAut V) (P₀ : Sylow 2 Γ) (dat : List (List ℕ × List ℕ))
    (hcov : ∀ s ∈ (P₀ : Subgroup Γ).map ρ, s * s = 1 → s ≠ 1 → ∃ d ∈ dat, ActsBy c s d.1)
    (hchk : chk2 n dat = true) {B : Subgroup (MulAut V)} (hB : B ≤ ρ.range) (hB1 : B ≠ ⊥)
    (hsq : ∀ s ∈ B, s * s = 1) (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v) :
    Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ n := by
  have h2 : IsPGroup 2 B := fun x => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hsq x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le ρ P₀ hB h2
  set e := (ρ g)⁻¹ with he
  have key := cube_bound_two (c := c) (B := B.map (MulAut.conj e).toMonoidHom) hg
    (fun h => hB1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj e).injective).1 h))
    (by rintro _ ⟨s, hs, rfl⟩; exact conj_mul_self e s (hsq s hs)) (quad_map_conj e hq)
    dat hcov hchk
  rw [Subgroup.card_map_of_injective (MulAut.conj e).injective] at key
  calc Nat.card B ^ 3 * Nat.card (fixV B) =
      Nat.card B ^ 3 * Nat.card (fixV (B.map (MulAut.conj e).toMonoidHom)) := by
        congr 1
        exact (card_fixV_map_conj e B).symm
    _ ≤ 2 ^ n := key

theorem cube9 {B : Subgroup (MulAut W9)} (hB : B ≤ rho9G.range) (hB1 : B ≠ ⊥)
    (hsq : ∀ s ∈ B, s * s = 1) (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v) :
    Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ 9 :=
  cube_of_cov1 (MaskCoords.std 9) rho9G sylSig9 dat9 (by rw [coe_sylSig9]; exact cov9)
    chk1_dat9 hB hB1 hsq hq

end CFSG.Quasithin.H13.Ch9.L34M

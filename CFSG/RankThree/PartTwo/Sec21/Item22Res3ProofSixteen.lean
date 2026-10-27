module

public import CFSG.RankThree.PartTwo.Sec21.Item22Res3ProofStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item22Res3Proof.Sixteen

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp sympForm)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSL StatedProj StatedScalars)
open Matrix

section Generic

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

theorem one_add_mul_self_of_char_two (h2 : (2 : F) = 0) {N : Matrix ι ι F} (hN : N * N = 0) :
    (1 + N) * (1 + N) = 1 := by
  have h2N : N + N = 0 := by rw [← two_smul F N, h2, zero_smul]
  simp only [add_mul, mul_add, one_mul, mul_one, hN, add_zero]
  rw [add_assoc, h2N, add_zero]

theorem det_one_add_of_char_two (h2 : (2 : F) = 0) {N : Matrix ι ι F} (hN : N * N = 0) :
    (1 + N).det = 1 := by
  have hsq := one_add_mul_self_of_char_two h2 hN
  have hd : (1 + N).det * (1 + N).det = 1 := by rw [← det_mul, hsq, det_one]
  have h0 : ((1 + N).det - 1) * ((1 + N).det - 1) = 0 := by
    linear_combination hd - (1 + N).det * h2 + h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)

variable {W : Type*} [AddCommGroup W]

@[expose] def unipHom (N : W →+ Matrix ι ι F) (hN : ∀ w w', N w * N w' = 0) :
    Multiplicative W →* GL ι F where
  toFun w := ⟨1 + N w.toAdd, 1 - N w.toAdd,
    by simp only [add_mul, mul_sub, one_mul, mul_one, hN]; abel,
    by simp only [sub_mul, mul_add, one_mul, mul_one, hN, sub_zero]; abel⟩
  map_one' := Units.ext (by simp)
  map_mul' w w' := Units.ext (by
    simp only [toAdd_mul, map_add, Units.val_mul, add_mul, mul_add, one_mul, mul_one, hN,
      add_zero]
    abel)

theorem coe_unipHom (N : W →+ Matrix ι ι F) (hN : ∀ w w', N w * N w' = 0)
    (w : Multiplicative W) : ((unipHom N hN w : GL ι F) : Matrix ι ι F) = 1 + N w.toAdd := rfl

theorem exists_elemAbelian_of_injective {Y : Type*} [Finite W] [Group Y]
    (h2 : ∀ w : W, w + w = 0) (f : Multiplicative W →* Y) (hf : Function.Injective f) :
    ∃ E : Subgroup Y, IsElemAbelian 2 E ∧ Nat.card E = Nat.card W := by
  refine ⟨f.range, ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, a, rfl⟩ := x
    obtain ⟨_, b, rfl⟩ := y
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, sq, show a * a = 1 from h2 a.toAdd, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    rfl

theorem offdiag_eq_zero_of_mem_center {g : GL ι F} (h : g ∈ Subgroup.center (GL ι F))
    {i j : ι} (hij : i ≠ j) : (g : Matrix ι ι F) i j = 0 := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, rfl⟩ := h
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]

theorem offdiag_eq_zero_of_mk_eq_one {g : GL ι F} (h : ProjGenLinGroup.mk g = 1) {i j : ι}
    (hij : i ≠ j) : (g : Matrix ι ι F) i j = 0 :=
  offdiag_eq_zero_of_mem_center (ProjGenLinGroup.mk_eq_one.mp h) hij

theorem offdiag_eq_zero_of_mem_statedScalars {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {g : GL ι K} (h : g ∈ StatedScalars ι K) {i j : ι} (hij : i ≠ j) :
    (g : Matrix ι ι K) i j = 0 := by
  rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar] at h
  exact offdiag_eq_zero_of_mem_center h hij

theorem e16_of_injective {Y T W : Type*} [Group Y] [Group T] [AddCommGroup W] [Finite W]
    (h2 : ∀ w : W, w + w = 0) (hW : Nat.card W = 2 ^ 4) (e : Y ≃* T)
    (f : Multiplicative W →* T) (hf : Function.Injective f) :
    ∃ E : Subgroup Y, IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 := by
  obtain ⟨E, hE, hc⟩ := exists_elemAbelian_of_injective h2 (e.symm.toMonoidHom.comp f)
    (e.symm.injective.comp hf)
  exact ⟨E, hE, hc.trans hW⟩

end Generic

abbrev GF4 : Type := GaloisField 2 2

theorem card_GF4 : Nat.card GF4 = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem two_GF4 : (2 : GF4) = 0 := CharTwo.two_eq_zero

theorem add_self_GF4 (w : GF4 × GF4) : w + w = 0 :=
  Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)

theorem card_GF4_prod : Nat.card (GF4 × GF4) = 2 ^ 4 := by
  rw [Nat.card_prod, card_GF4]
  norm_num

@[expose] noncomputable def nSL3 : GF4 × GF4 →+ Matrix (Fin 3) (Fin 3) GF4 where
  toFun w := !![0, 0, w.1; 0, 0, w.2; 0, 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' w w' := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem nSL3_mul (w w' : GF4 × GF4) : nSL3 w * nSL3 w' = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL3, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] noncomputable def sl3Hom : Multiplicative (GF4 × GF4) →* SL3 2 where
  toFun w := ⟨1 + nSL3 w.toAdd, det_one_add_of_char_two two_GF4 (nSL3_mul _ _)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' w w' := Subtype.ext (by
    change 1 + nSL3 (w * w').toAdd = (1 + nSL3 w.toAdd) * (1 + nSL3 w'.toAdd)
    simp only [toAdd_mul, map_add, add_mul, mul_add, one_mul, mul_one, nSL3_mul, add_zero]
    abel)

theorem coe_sl3Hom (w : Multiplicative (GF4 × GF4)) :
    ((sl3Hom w : SL3 2) : Matrix (Fin 3) (Fin 3) GF4) = 1 + nSL3 w.toAdd := rfl

theorem sl3Hom_injective : Function.Injective sl3Hom := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h := congrArg (fun A : SL3 2 => (A : Matrix (Fin 3) (Fin 3) GF4)) hw
  simp only [coe_sl3Hom, Matrix.SpecialLinearGroup.coe_one, add_eq_left] at h
  have h1 := congrFun (congrFun h 0) 2
  have h2 := congrFun (congrFun h 1) 2
  simp [nSL3] at h1 h2
  rw [← ofAdd_toAdd w]
  have : w.toAdd = 0 := Prod.ext h1 h2
  rw [this, ofAdd_zero]

@[expose] noncomputable def nSp : GF4 × GF4 →+ Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) GF4 where
  toFun w := Matrix.fromBlocks 0 (Matrix.diagonal ![w.1, w.2]) 0 0
  map_zero' := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
  map_add' w w' := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp

theorem nSp_mul (w w' : GF4 × GF4) : nSp w * nSp w' = 0 := by
  simp [nSp, Matrix.fromBlocks_multiply, Matrix.fromBlocks_zero]

theorem nSp_symplectic (w : GF4 × GF4) :
    (1 + nSp w)ᵀ * sympForm 2 GF4 * (1 + nSp w) = sympForm 2 GF4 := by
  simp only [nSp, AddMonoidHom.coe_mk, ZeroHom.coe_mk, sympForm]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_add, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.diagonal_transpose]

@[expose] noncomputable def spHom : Multiplicative (GF4 × GF4) →* projSp 2 GF4 :=
  (ProjGenLinGroup.mk.comp (unipHom nSp nSp_mul)).codRestrict (projSp 2 GF4) fun w =>
    ⟨unipHom nSp nSp_mul w, Subgroup.subset_closure (nSp_symplectic w.toAdd), rfl⟩

theorem spHom_injective : Function.Injective spHom := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h : ProjGenLinGroup.mk (unipHom nSp nSp_mul w) = 1 := congrArg Subtype.val hw
  have h1 := offdiag_eq_zero_of_mk_eq_one h (i := Sum.inl 0) (j := Sum.inr 0) (by simp)
  have h2 := offdiag_eq_zero_of_mk_eq_one h (i := Sum.inl 1) (j := Sum.inr 1) (by simp)
  simp [coe_unipHom, nSp] at h1 h2
  rw [← ofAdd_toAdd w]
  have : w.toAdd = 0 := Prod.ext h1 h2
  rw [this, ofAdd_zero]

abbrev GF16 : Type := GaloisField 2 (2 * 2)

theorem card_GF16 : Nat.card GF16 = 16 := by
  rw [GaloisField.card 2 (2 * 2) (by norm_num)]
  norm_num

theorem two_GF16 : (2 : GF16) = 0 := CharTwo.two_eq_zero

theorem exists_omega : ∃ ω : GF16, ω ^ 2 + ω + 1 = 0 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hu : Nat.card GF16ˣ = 15 := by rw [Nat.card_units, card_GF16]
  obtain ⟨u, hu3⟩ := exists_prime_orderOf_dvd_card' (G := GF16ˣ) 3 (by rw [hu]; norm_num)
  refine ⟨(u : GF16), ?_⟩
  have h3 : (u : GF16) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu3, pow_orderOf_eq_one, Units.val_one]
  have h1 : (u : GF16) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu3
    omega
  have h0 : ((u : GF16) - 1) * ((u : GF16) ^ 2 + u + 1) = 0 := by linear_combination h3
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr h1)

@[expose] noncomputable def omega16 : GF16 := exists_omega.choose

theorem omega16_sq : omega16 ^ 2 + omega16 + 1 = 0 := exists_omega.choose_spec

theorem omega16_pow : omega16 ^ 2 ^ 2 = omega16 := by
  have h3 : omega16 ^ 3 = 1 := by linear_combination (omega16 - 1) * omega16_sq
  calc omega16 ^ 2 ^ 2 = omega16 ^ 3 * omega16 := by ring
    _ = omega16 := by rw [h3, one_mul]

@[expose] noncomputable def sOf : ZMod 2 × ZMod 2 →+ GF16 where
  toFun ab := algebraMap (ZMod 2) GF16 ab.1 + algebraMap (ZMod 2) GF16 ab.2 * omega16
  map_zero' := by simp
  map_add' ab ab' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem zmod_two_pow : ∀ a : ZMod 2, a ^ 2 ^ 2 = a := by decide

theorem sOf_pow (ab : ZMod 2 × ZMod 2) : (sOf ab) ^ 2 ^ 2 = sOf ab := by
  simp only [sOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [add_pow_char_pow, mul_pow, ← map_pow, ← map_pow, zmod_two_pow, zmod_two_pow,
    omega16_pow]

theorem sOf_pow_four (ab : ZMod 2 × ZMod 2) : sOf ab ^ 4 = sOf ab := sOf_pow ab

theorem one_add_sOf_pow_four (ab : ZMod 2 × ZMod 2) : (1 + sOf ab) ^ 4 = 1 + sOf ab := by
  have h : (1 + sOf ab) ^ 2 ^ 2 = 1 + sOf ab := by rw [add_pow_char_pow, one_pow, sOf_pow]
  exact h

theorem sOf_eq_zero {ab : ZMod 2 × ZMod 2} (h : sOf ab = 0) : ab = 0 := by
  have hom := omega16_sq
  obtain ⟨a, b⟩ := ab
  simp only [sOf, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
  rcases zmod_two_cases a with rfl | rfl <;> rcases zmod_two_cases b with rfl | rfl
  · rfl
  · simp only [map_zero, map_one, zero_add, one_mul] at h
    rw [h] at hom
    simp at hom
  · simp at h
  · simp only [map_one, one_mul] at h
    have : omega16 = 1 := by linear_combination h - two_GF16
    rw [this] at hom
    have : (1 : GF16) = 0 := by linear_combination hom - two_GF16
    exact absurd this one_ne_zero

theorem add_self_zmod (w : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) : w + w = 0 := by
  revert w
  decide

theorem card_zmod_four : Nat.card ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) = 2 ^ 4 := by
  simp

@[expose] noncomputable def n14 : Matrix (Fin 4) (Fin 4) GF16 :=
  !![1, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] noncomputable def n24 : Matrix (Fin 4) (Fin 4) GF16 :=
  !![0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 1, 1; 0, 0, 1, 1]

theorem n14_mul_n14 : n14 * n14 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n14, Matrix.mul_apply, Fin.sum_univ_four, two_GF16, one_add_one_eq_two]

theorem n14_mul_n24 : n14 * n24 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [n14, n24, Matrix.mul_apply, Fin.sum_univ_four]

theorem n24_mul_n14 : n24 * n14 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [n14, n24, Matrix.mul_apply, Fin.sum_univ_four]

theorem n24_mul_n24 : n24 * n24 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n24, Matrix.mul_apply, Fin.sum_univ_four, two_GF16, one_add_one_eq_two]

@[expose] noncomputable def nSU4 :
    (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) →+ Matrix (Fin 4) (Fin 4) GF16 where
  toFun w := sOf w.1 • n14 + sOf w.2 • n24
  map_zero' := by simp
  map_add' w w' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel

theorem nSU4_mul (w w' : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) : nSU4 w * nSU4 w' = 0 := by
  simp [nSU4, add_mul, mul_add, n14_mul_n14, n14_mul_n24, n24_mul_n14, n24_mul_n24]

theorem nSU4_unitary (w : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) :
    ((1 + nSU4 w).map (· ^ 2 ^ 2))ᵀ * (1 + nSU4 w) = 1 := by
  have hmap : ((1 + nSU4 w).map (· ^ 2 ^ 2))ᵀ = 1 + nSU4 w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nSU4, n14, n24, sOf_pow_four, one_add_sOf_pow_four]
  rw [hmap, one_add_mul_self_of_char_two two_GF16 (nSU4_mul w w)]

@[expose] noncomputable def su4Hom :
    Multiplicative ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) →* projSU 4 2 2 :=
  (ProjGenLinGroup.mk.comp (unipHom nSU4 nSU4_mul)).codRestrict (projSU 4 2 2) fun w =>
    ⟨unipHom nSU4 nSU4_mul w,
      Subgroup.subset_closure ⟨Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact det_one_add_of_char_two two_GF16 (nSU4_mul _ _)), nSU4_unitary w.toAdd⟩, rfl⟩

theorem su4Hom_injective : Function.Injective su4Hom := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h : ProjGenLinGroup.mk (unipHom nSU4 nSU4_mul w) = 1 := congrArg Subtype.val hw
  have h1 := offdiag_eq_zero_of_mk_eq_one h (i := 0) (j := 1) (by decide)
  have h2 := offdiag_eq_zero_of_mk_eq_one h (i := 2) (j := 3) (by decide)
  change (1 + nSU4 w.toAdd) 0 1 = 0 at h1
  change (1 + nSU4 w.toAdd) 2 3 = 0 at h2
  simp [nSU4, n14, n24] at h1 h2
  rw [← ofAdd_toAdd w]
  have : w.toAdd = 0 := Prod.ext (sOf_eq_zero h1) (sOf_eq_zero h2)
  rw [this, ofAdd_zero]

@[expose] noncomputable def n15 : Matrix (Fin 5) (Fin 5) GF16 :=
  !![1, 1, 0, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0]

@[expose] noncomputable def n25 : Matrix (Fin 5) (Fin 5) GF16 :=
  !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 0]

theorem n15_mul_n15 : n15 * n15 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n15, Matrix.mul_apply, Fin.sum_univ_five, two_GF16, one_add_one_eq_two]

theorem n15_mul_n25 : n15 * n25 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [n15, n25, Matrix.mul_apply, Fin.sum_univ_five]

theorem n25_mul_n15 : n25 * n15 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [n15, n25, Matrix.mul_apply, Fin.sum_univ_five]

theorem n25_mul_n25 : n25 * n25 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [n25, Matrix.mul_apply, Fin.sum_univ_five, two_GF16, one_add_one_eq_two]

@[expose] noncomputable def nSU5 :
    (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2) →+ Matrix (Fin 5) (Fin 5) GF16 where
  toFun w := sOf w.1 • n15 + sOf w.2 • n25
  map_zero' := by simp
  map_add' w w' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel

theorem nSU5_mul (w w' : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) : nSU5 w * nSU5 w' = 0 := by
  simp [nSU5, add_mul, mul_add, n15_mul_n15, n15_mul_n25, n25_mul_n15, n25_mul_n25]

theorem nSU5_unitary (w : (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) :
    ((1 + nSU5 w).map (· ^ 2 ^ 2))ᵀ * (1 + nSU5 w) = 1 := by
  have hmap : ((1 + nSU5 w).map (· ^ 2 ^ 2))ᵀ = 1 + nSU5 w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nSU5, n15, n25, sOf_pow_four, one_add_sOf_pow_four]
  rw [hmap, one_add_mul_self_of_char_two two_GF16 (nSU5_mul w w)]

@[expose] noncomputable def su5Hom :
    Multiplicative ((ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)) →* projSU 5 2 2 :=
  (ProjGenLinGroup.mk.comp (unipHom nSU5 nSU5_mul)).codRestrict (projSU 5 2 2) fun w =>
    ⟨unipHom nSU5 nSU5_mul w,
      Subgroup.subset_closure ⟨Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact det_one_add_of_char_two two_GF16 (nSU5_mul _ _)), nSU5_unitary w.toAdd⟩, rfl⟩

theorem su5Hom_injective : Function.Injective su5Hom := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h : ProjGenLinGroup.mk (unipHom nSU5 nSU5_mul w) = 1 := congrArg Subtype.val hw
  have h1 := offdiag_eq_zero_of_mk_eq_one h (i := 0) (j := 1) (by decide)
  have h2 := offdiag_eq_zero_of_mk_eq_one h (i := 2) (j := 3) (by decide)
  change (1 + nSU5 w.toAdd) 0 1 = 0 at h1
  change (1 + nSU5 w.toAdd) 2 3 = 0 at h2
  simp [nSU5, n15, n25] at h1 h2
  rw [← ofAdd_toAdd w]
  have : w.toAdd = 0 := Prod.ext (sOf_eq_zero h1) (sOf_eq_zero h2)
  rw [this, ofAdd_zero]

section StatedSL

variable {K : Type} [Field K]

@[expose] def nSL4 : (K × K) × (K × K) →+ Matrix (Fin 4) (Fin 4) K where
  toFun w := !![0, 0, w.1.1, w.1.2; 0, 0, w.2.1, w.2.2; 0, 0, 0, 0; 0, 0, 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' w w' := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem nSL4_mul (w w' : (K × K) × (K × K)) : nSL4 w * nSL4 w' = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL4, Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def nSL5 : (K × K) × (K × K) →+ Matrix (Fin 5) (Fin 5) K where
  toFun w := !![0, 0, w.1.1, w.1.2, 0; 0, 0, w.2.1, w.2.2, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0]
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_add' w w' := by ext i j; fin_cases i <;> fin_cases j <;> simp

theorem nSL5_mul (w w' : (K × K) × (K × K)) : nSL5 w * nSL5 w' = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nSL5, Matrix.mul_apply, Fin.sum_univ_five]

theorem two_eq_zero_of_card [Finite K] (hK : Nat.card K = 2 ^ 1) : (2 : K) = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.cast_card_eq_zero K
  rw [Fintype.card_eq_nat_card, hK] at h
  exact_mod_cast h

variable (h2 : (2 : K) = 0)
include h2

@[expose] noncomputable def sl4Hom :
    Multiplicative ((K × K) × (K × K)) →* StatedProj (StatedSL 4 K) :=
  (QuotientGroup.mk' _).comp ((unipHom nSL4 nSL4_mul).codRestrict (StatedSL 4 K) fun _ =>
    Subgroup.subset_closure (det_one_add_of_char_two h2 (nSL4_mul _ _)))

theorem sl4Hom_injective : Function.Injective (sl4Hom h2) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h : unipHom nSL4 nSL4_mul w ∈ StatedScalars (Fin 4) K :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hw)
  have e02 := offdiag_eq_zero_of_mem_statedScalars h (i := 0) (j := 2) (by decide)
  have e03 := offdiag_eq_zero_of_mem_statedScalars h (i := 0) (j := 3) (by decide)
  have e12 := offdiag_eq_zero_of_mem_statedScalars h (i := 1) (j := 2) (by decide)
  have e13 := offdiag_eq_zero_of_mem_statedScalars h (i := 1) (j := 3) (by decide)
  change (1 + nSL4 w.toAdd) 0 2 = 0 at e02
  change (1 + nSL4 w.toAdd) 0 3 = 0 at e03
  change (1 + nSL4 w.toAdd) 1 2 = 0 at e12
  change (1 + nSL4 w.toAdd) 1 3 = 0 at e13
  simp [nSL4] at e02 e03 e12 e13
  rw [← ofAdd_toAdd w]
  have : w.toAdd = 0 := Prod.ext (Prod.ext e02 e03) (Prod.ext e12 e13)
  rw [this, ofAdd_zero]

@[expose] noncomputable def sl5Hom :
    Multiplicative ((K × K) × (K × K)) →* StatedProj (StatedSL 5 K) :=
  (QuotientGroup.mk' _).comp ((unipHom nSL5 nSL5_mul).codRestrict (StatedSL 5 K) fun _ =>
    Subgroup.subset_closure (det_one_add_of_char_two h2 (nSL5_mul _ _)))

theorem sl5Hom_injective : Function.Injective (sl5Hom h2) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  have h : unipHom nSL5 nSL5_mul w ∈ StatedScalars (Fin 5) K :=
    Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp hw)
  have e02 := offdiag_eq_zero_of_mem_statedScalars h (i := 0) (j := 2) (by decide)
  have e03 := offdiag_eq_zero_of_mem_statedScalars h (i := 0) (j := 3) (by decide)
  have e12 := offdiag_eq_zero_of_mem_statedScalars h (i := 1) (j := 2) (by decide)
  have e13 := offdiag_eq_zero_of_mem_statedScalars h (i := 1) (j := 3) (by decide)
  change (1 + nSL5 w.toAdd) 0 2 = 0 at e02
  change (1 + nSL5 w.toAdd) 0 3 = 0 at e03
  change (1 + nSL5 w.toAdd) 1 2 = 0 at e12
  change (1 + nSL5 w.toAdd) 1 3 = 0 at e13
  simp [nSL5] at e02 e03 e12 e13
  rw [← ofAdd_toAdd w]
  have : w.toAdd = 0 := Prod.ext (Prod.ext e02 e03) (Prod.ext e12 e13)
  rw [this, ofAdd_zero]

end StatedSL

end CFSG.RankThree.PartTwo.Sec21.Item22Res3Proof.Sixteen

namespace CFSG.RankThree.PartTwo.Sec21

open Item22Res3Proof.Sixteen

theorem list228Sixteen : List228Sixteen := by
  intro Y _ _ hY
  rcases hY with he | he | he | he | h | h
  · obtain ⟨e⟩ := he
    exact e16_of_injective add_self_GF4 card_GF4_prod e sl3Hom sl3Hom_injective
  · obtain ⟨e⟩ := he
    exact e16_of_injective add_self_GF4 card_GF4_prod e spHom spHom_injective
  · obtain ⟨e⟩ := he
    exact e16_of_injective add_self_zmod card_zmod_four e su4Hom su4Hom_injective
  · obtain ⟨e⟩ := he
    exact e16_of_injective add_self_zmod card_zmod_four e su5Hom su5Hom_injective
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have h2 := two_eq_zero_of_card hK
    exact e16_of_injective (fun w : (K × K) × (K × K) => by rw [← two_smul K w, h2, zero_smul])
      (by simp only [Nat.card_prod, hK]; norm_num) e (sl4Hom h2) (sl4Hom_injective h2)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have h2 := two_eq_zero_of_card hK
    exact e16_of_injective (fun w : (K × K) × (K × K) => by rw [← two_smul K w, h2, zero_smul])
      (by simp only [Nat.card_prod, hK]; norm_num) e (sl5Hom h2) (sl5Hom_injective h2)

end CFSG.RankThree.PartTwo.Sec21

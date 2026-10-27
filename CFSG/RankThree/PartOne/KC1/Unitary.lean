module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.RankThree.PartOne.KC1

open Matrix

abbrev SL5 (L : Type*) [Field L] : Type _ := SpecialLinearGroup (Fin 5) L

section Unitary

variable {L : Type*} [Field L]

@[expose] def tauSL : SL5 L →* SL5 L where
  toFun B := ⟨(((B⁻¹ : SL5 L) : Matrix (Fin 5) (Fin 5) L))ᵀ, by
    rw [det_transpose]; exact (B⁻¹).2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' A B := by
    apply Subtype.ext
    show (((A * B)⁻¹ : SL5 L) : Matrix (Fin 5) (Fin 5) L)ᵀ =
      ((A⁻¹ : SL5 L) : Matrix (Fin 5) (Fin 5) L)ᵀ * ((B⁻¹ : SL5 L) : Matrix (Fin 5) (Fin 5) L)ᵀ
    rw [_root_.mul_inv_rev, SpecialLinearGroup.coe_mul, transpose_mul]

theorem coe_tauSL (B : SL5 L) :
    ((tauSL B : SL5 L) : Matrix (Fin 5) (Fin 5) L) = ((B⁻¹ : SL5 L) : Matrix (Fin 5) (Fin 5) L)ᵀ :=
  rfl

variable (Fr₂ : L →+* L)

@[expose] def Theta : SL5 L →* SL5 L := tauSL.comp (SpecialLinearGroup.map Fr₂)

@[expose] def U : Subgroup (SL5 L) := (Theta Fr₂).eqLocus (MonoidHom.id _)

theorem mem_U_iff' {A : SL5 L} :
    A ∈ U Fr₂ ↔ tauSL (SpecialLinearGroup.map Fr₂ A) = A := Iff.rfl

theorem mem_U_iff {A : SL5 L} :
    A ∈ U Fr₂ ↔
      ((A : Matrix (Fin 5) (Fin 5) L).map Fr₂)ᵀ * (A : Matrix (Fin 5) (Fin 5) L) = 1 := by
  set B : Matrix (Fin 5) (Fin 5) L := (A : Matrix (Fin 5) (Fin 5) L).map Fr₂ with hB
  have hBdet : B.det = 1 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, A.det_coe, map_one]
  have hadj1 : B * B.adjugate = 1 := by rw [mul_adjugate, hBdet, one_smul]
  have hadj2 : B.adjugate * B = 1 := by rw [adjugate_mul, hBdet, one_smul]
  have hT : ((Theta Fr₂ A : SL5 L) : Matrix (Fin 5) (Fin 5) L) = B.adjugateᵀ := by
    show ((((SpecialLinearGroup.map Fr₂ A)⁻¹ : SL5 L)) : Matrix (Fin 5) (Fin 5) L)ᵀ = _
    rw [SpecialLinearGroup.coe_inv, SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have key : A ∈ U Fr₂ ↔ B.adjugateᵀ = (A : Matrix (Fin 5) (Fin 5) L) := by
    show Theta Fr₂ A = A ↔ _
    constructor
    · intro h
      exact hT.symm.trans (congrArg (fun X : SL5 L => (X : Matrix (Fin 5) (Fin 5) L)) h)
    · intro h
      exact Subtype.ext (hT.trans h)
  rw [key]
  constructor
  · intro h
    have h1 : B.adjugate = (A : Matrix (Fin 5) (Fin 5) L)ᵀ := by rw [← h, transpose_transpose]
    have h2 : B * (A : Matrix (Fin 5) (Fin 5) L)ᵀ = 1 := by rw [← h1, hadj1]
    have h3 : (A : Matrix (Fin 5) (Fin 5) L) * Bᵀ = 1 := by
      have := congrArg transpose h2
      simpa [transpose_mul] using this
    exact mul_eq_one_comm.1 h3
  · intro h
    have h2 : (A : Matrix (Fin 5) (Fin 5) L) * Bᵀ = 1 := mul_eq_one_comm.1 h
    have h3 : B * (A : Matrix (Fin 5) (Fin 5) L)ᵀ = 1 := by
      have := congrArg transpose h2
      simpa [transpose_mul] using this
    have h4 : B.adjugate = (A : Matrix (Fin 5) (Fin 5) L)ᵀ := by
      calc B.adjugate = B.adjugate * (B * (A : Matrix (Fin 5) (Fin 5) L)ᵀ) := by rw [h3, mul_one]
        _ = (B.adjugate * B) * (A : Matrix (Fin 5) (Fin 5) L)ᵀ := by rw [Matrix.mul_assoc]
        _ = (A : Matrix (Fin 5) (Fin 5) L)ᵀ := by rw [hadj2, one_mul]
    rw [h4, transpose_transpose]

theorem tauSL_tauSL (B : SL5 L) : tauSL (tauSL B) = B := by
  apply Subtype.ext
  rw [coe_tauSL, SpecialLinearGroup.coe_inv, coe_tauSL, ← adjugate_transpose,
    ← SpecialLinearGroup.coe_inv, transpose_transpose, SpecialLinearGroup.coe_inv,
    ← SpecialLinearGroup.coe_inv B⁻¹, inv_inv]

theorem tauSL_map (f : L →+* L) (B : SL5 L) :
    tauSL (SpecialLinearGroup.map f B) = SpecialLinearGroup.map f (tauSL B) := by
  apply Subtype.ext
  have h := RingHom.map_adjugate f (B : Matrix (Fin 5) (Fin 5) L)
  simp only [RingHom.mapMatrix_apply] at h
  rw [coe_tauSL, SpecialLinearGroup.coe_inv, SpecialLinearGroup.map_apply_coe,
    SpecialLinearGroup.map_apply_coe, coe_tauSL, SpecialLinearGroup.coe_inv,
    RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, ← h, ← transpose_map]

theorem map_map_SL (f : L →+* L) (A : SL5 L) :
    SpecialLinearGroup.map f (SpecialLinearGroup.map f A) =
      SpecialLinearGroup.map (f.comp f) A := by
  apply Subtype.ext
  ext i j
  simp [SpecialLinearGroup.map_apply_coe]

theorem map_comp_of_mem_U {A : SL5 L} (hA : A ∈ U Fr₂) :
    SpecialLinearGroup.map (Fr₂.comp Fr₂) A = A := by
  have h1 : tauSL (SpecialLinearGroup.map Fr₂ A) = A := (mem_U_iff' (Fr₂ := Fr₂)).1 hA
  calc SpecialLinearGroup.map (Fr₂.comp Fr₂) A
      = SpecialLinearGroup.map Fr₂ (SpecialLinearGroup.map Fr₂ A) := (map_map_SL Fr₂ A).symm
    _ = tauSL (tauSL (SpecialLinearGroup.map Fr₂ (SpecialLinearGroup.map Fr₂ A))) :=
        (tauSL_tauSL _).symm
    _ = tauSL (SpecialLinearGroup.map Fr₂ (tauSL (SpecialLinearGroup.map Fr₂ A))) := by
        rw [tauSL_map]
    _ = tauSL (SpecialLinearGroup.map Fr₂ A) :=
        congrArg (fun X : SL5 L => tauSL (SpecialLinearGroup.map Fr₂ X)) h1
    _ = A := h1

variable (L) in
@[expose] def Dgrp (Q : ℕ) : Subgroup (SL5 L) where
  carrier := {A | ∃ d : Fin 5 → L, (∀ i, d i ^ (Q + 1) = 1) ∧
    (A : Matrix (Fin 5) (Fin 5) L) = diagonal d}
  one_mem' := ⟨fun _ => 1, fun _ => one_pow _, by simp⟩
  mul_mem' := by
    rintro A B ⟨d, hd, hA⟩ ⟨e, he, hB⟩
    exact ⟨fun i => d i * e i, fun i => by rw [mul_pow, hd, he, one_mul], by
      rw [SpecialLinearGroup.coe_mul, hA, hB, diagonal_mul_diagonal]⟩
  inv_mem' := by
    rintro A ⟨d, hd, hA⟩
    refine ⟨fun i => ∏ j ∈ Finset.univ.erase i, d j, fun i => ?_, ?_⟩
    · rw [← Finset.prod_pow]; exact Finset.prod_eq_one (fun j _ => hd j)
    · rw [SpecialLinearGroup.coe_inv, hA, adjugate_diagonal]

variable {Fr₂} {Q : ℕ}

theorem Dgrp_offDiag {A : SL5 L} (hA : A ∈ Dgrp L Q) (i j : Fin 5) (hij : i ≠ j) :
    (A : Matrix (Fin 5) (Fin 5) L) i j = 0 := by
  obtain ⟨d, -, h⟩ := hA
  rw [h, diagonal_apply_ne _ hij]

theorem diagonal_unitary (hFr : ∀ x, Fr₂ x = x ^ Q) {e : Fin 5 → L}
    (he : ∀ i, e i ^ (Q + 1) = 1) : ((diagonal e).map Fr₂)ᵀ * diagonal e = 1 := by
  rw [diagonal_map (map_zero Fr₂), diagonal_transpose, diagonal_mul_diagonal]
  have : (fun i => Fr₂ (e i) * e i) = fun _ => (1 : L) := by
    funext i; rw [hFr, ← pow_succ]; exact he i
  rw [this, diagonal_one]

theorem Dgrp_le_U (hFr : ∀ x, Fr₂ x = x ^ Q) : Dgrp L Q ≤ U Fr₂ := by
  rintro A ⟨d, hd, hA⟩
  rw [mem_U_iff, hA]
  exact diagonal_unitary hFr hd

theorem unitary_mul {A B : Matrix (Fin 5) (Fin 5) L} (hA : (A.map Fr₂)ᵀ * A = 1)
    (hB : (B.map Fr₂)ᵀ * B = 1) : ((A * B).map Fr₂)ᵀ * (A * B) = 1 := by
  rw [Matrix.map_mul, transpose_mul]
  calc (B.map Fr₂)ᵀ * (A.map Fr₂)ᵀ * (A * B)
      = (B.map Fr₂)ᵀ * ((A.map Fr₂)ᵀ * A) * B := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

theorem det_pow_of_unitary (hFr : ∀ x, Fr₂ x = x ^ Q) {A : Matrix (Fin 5) (Fin 5) L}
    (hA : (A.map Fr₂)ᵀ * A = 1) : A.det ^ (Q + 1) = 1 := by
  have h := congrArg Matrix.det hA
  rw [det_mul, det_transpose, det_one, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hFr] at h
  rw [pow_succ]; exact h

variable (L) in
@[expose] def Pmat : Matrix (Fin 5) (Fin 5) L := (finRotate 5).permMatrix L

theorem Pmat_apply (i j : Fin 5) :
    Pmat L i j = if finRotate 5 i = j then 1 else 0 := by
  simp [Pmat, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

theorem det_Pmat : (Pmat L).det = 1 := by
  rw [Pmat, det_permutation, sign_finRotate]; simp

variable (L) in
@[expose] def P : SL5 L := ⟨Pmat L, det_Pmat⟩

theorem coe_P : ((P L : SL5 L) : Matrix (Fin 5) (Fin 5) L) = Pmat L := rfl

theorem Pmat_mul_diagonal (e : Fin 5 → L) :
    Pmat L * diagonal e = diagonal (fun i => e (finRotate 5 i)) * Pmat L := by
  ext i j
  rw [mul_diagonal, diagonal_mul, Pmat_apply]
  by_cases h : finRotate 5 i = j
  · subst h; simp
  · simp only [h, ↓reduceIte, zero_mul, mul_zero]

theorem Pmat_transpose_mul : (Pmat L)ᵀ * Pmat L = 1 := by
  rw [Pmat, transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]

theorem P_mem_U (Fr₂ : L →+* L) : P L ∈ U Fr₂ := by
  rw [mem_U_iff]
  have : (Pmat L).map Fr₂ = Pmat L := by
    ext i j
    simp only [Matrix.map_apply, Pmat_apply, apply_ite Fr₂, map_one, map_zero]
  rw [coe_P, this, Pmat_transpose_mul]

theorem P_notMem_Dgrp (Q : ℕ) : P L ∉ Dgrp L Q := by
  rintro ⟨d, hd, h⟩
  have h1 := congrFun (congrFun h 0) 1
  rw [coe_P, Pmat_apply, diagonal_apply_ne _ (by decide)] at h1
  have h2 : finRotate 5 0 = 1 := by decide
  simp [h2] at h1

theorem P_pow_five : (P L) ^ 5 = 1 := by
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, coe_P, SpecialLinearGroup.coe_one]
  have h : Pmat L = permMatrixHom (R := L) (finRotate 5)⁻¹ := by
    simp [Pmat, permMatrixHom_apply]
  have h5 : ((finRotate 5)⁻¹) ^ 5 = 1 := by
    rw [inv_pow]; have : (finRotate 5) ^ 5 = 1 := by decide
    rw [this, inv_one]
  rw [h, ← map_pow, h5, map_one]

theorem orderOf_P : orderOf (P L) = 5 :=
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  orderOf_eq_prime P_pow_five (fun h => P_notMem_Dgrp 0 (h ▸ (Dgrp L 0).one_mem))

theorem P_conj_diag {h : SL5 L} {d : Fin 5 → L}
    (hh : (h : Matrix (Fin 5) (Fin 5) L) = diagonal d) :
    ((P L * h * (P L)⁻¹ : SL5 L) : Matrix (Fin 5) (Fin 5) L) =
      diagonal (fun i => d (finRotate 5 i)) := by
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hh, coe_P, Pmat_mul_diagonal,
    Matrix.mul_assoc]
  have h1 : Pmat L * (((P L)⁻¹ : SL5 L) : Matrix (Fin 5) (Fin 5) L) = 1 := by
    rw [← coe_P, ← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one]
  rw [h1, Matrix.mul_one]

theorem P_mem_normalizer (Q : ℕ) :
    P L ∈ Subgroup.normalizer (Dgrp L Q : Set (SL5 L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨d, hd, hh⟩
    exact ⟨fun i => d (finRotate 5 i), fun i => hd _, P_conj_diag hh⟩
  · rintro ⟨d, hd, hh⟩
    set e : Fin 5 → L := fun i => d ((finRotate 5).symm i) with he
    have hdet : (diagonal e).det = 1 := by
      rw [det_diagonal, he, Equiv.prod_comp (finRotate 5).symm d, ← det_diagonal, ← hh]
      exact (P L * h * (P L)⁻¹).2
    set h'' : SL5 L := ⟨diagonal e, hdet⟩ with hh''
    have h1 : P L * h'' * (P L)⁻¹ = P L * h * (P L)⁻¹ := by
      apply Subtype.ext
      rw [P_conj_diag (h := h'') (d := e) rfl, hh]
      congr 1
      funext i
      simp [he]
    have h2 : h'' = h := by
      have := mul_right_cancel h1
      exact mul_left_cancel this
    exact ⟨e, fun i => hd _, by rw [← h2]⟩

theorem zpowers_P_le_normalizer (Q : ℕ) :
    Subgroup.zpowers (P L) ≤ Subgroup.normalizer (Dgrp L Q : Set (SL5 L)) :=
  Subgroup.zpowers_le.2 (P_mem_normalizer Q)

variable (L Q) in
abbrev Mon : Type _ :=
  Dgrp L Q ⋊[(Dgrp L Q).normalizerMonoidHom.comp (Subgroup.inclusion (zpowers_P_le_normalizer Q))]
    Subgroup.zpowers (P L)

@[expose] def monHom : Mon L Q →* SL5 L :=
  SemidirectProduct.monoidHomSubgroup (zpowers_P_le_normalizer Q)

theorem monHom_apply (z : Mon L Q) : monHom z = (z.left : SL5 L) * (z.right : SL5 L) := rfl

theorem eq_one_of_mem_zpowers_P_of_mem_Dgrp (Q : ℕ) {g : SL5 L}
    (hg : g ∈ Subgroup.zpowers (P L)) (hD : g ∈ Dgrp L Q) : g = 1 := by
  have : Fact (Nat.card (Subgroup.zpowers (P L))).Prime :=
    ⟨by rw [Nat.card_zpowers, orderOf_P]; exact Nat.prime_five⟩
  rcases ((Dgrp L Q).subgroupOf (Subgroup.zpowers (P L))).eq_bot_or_eq_top_of_prime_card with h | h
  · have h1 : (⟨g, hg⟩ : Subgroup.zpowers (P L)) ∈ (Dgrp L Q).subgroupOf (Subgroup.zpowers (P L)) :=
      hD
    rw [h, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val h1
  · exfalso
    have h1 : (⟨P L, Subgroup.mem_zpowers _⟩ : Subgroup.zpowers (P L)) ∈
        (Dgrp L Q).subgroupOf (Subgroup.zpowers (P L)) := by rw [h]; trivial
    exact P_notMem_Dgrp Q h1

theorem monHom_injective : Function.Injective (monHom (L := L) (Q := Q)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  rw [monHom_apply] at hz
  have h1 : (z.right : SL5 L) = ((z.left : SL5 L))⁻¹ := eq_inv_of_mul_eq_one_right hz
  have h2 : (z.right : SL5 L) = 1 :=
    eq_one_of_mem_zpowers_P_of_mem_Dgrp Q z.right.2 (h1 ▸ (Dgrp L Q).inv_mem z.left.2)
  have h3 : (z.left : SL5 L) = 1 := by rw [h2, mul_one] at hz; exact hz
  apply SemidirectProduct.ext
  · exact Subtype.ext h3
  · exact Subtype.ext h2

theorem card_Mon : Nat.card (Mon L Q) = Nat.card (Dgrp L Q) * 5 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod, Nat.card_zpowers, orderOf_P]

theorem monHom_mem_U (hFr : ∀ x, Fr₂ x = x ^ Q) (z : Mon L Q) : monHom z ∈ U Fr₂ := by
  rw [monHom_apply]
  exact (U Fr₂).mul_mem (Dgrp_le_U hFr z.left.2)
    ((Subgroup.zpowers_le.2 (P_mem_U Fr₂)) z.right.2)

section DFT

theorem sum_pow_five_eq_one [CharP L 2] {r : L} (hr : r = 1) :
    ∑ j : Fin 5, r ^ (j : ℕ) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => r ^ j) 5]
  subst hr
  simp
  have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
  linear_combination 2 * h2

theorem sum_pow_five_eq_zero {r : L} (hr : r ^ 5 = 1) (hr1 : r ≠ 1) :
    ∑ j : Fin 5, r ^ (j : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => r ^ j) 5]
  have h1 := geom_sum_mul r 5
  rw [hr, sub_self] at h1
  exact (mul_eq_zero.1 h1).resolve_right (sub_ne_zero.2 hr1)

@[expose] def Fmat (ζ : L) : Matrix (Fin 5) (Fin 5) L :=
  Matrix.of fun i j => ζ ^ ((i : ℕ) * (j : ℕ))

theorem Fmat_unitary [CharP L 2] (hFr : ∀ x, Fr₂ x = x ^ Q) {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    (hζQ : ζ ^ Q = ζ⁻¹) : ((Fmat ζ).map Fr₂)ᵀ * Fmat ζ = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hne : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hterm : ∀ j : Fin 5, ((Fmat ζ).map Fr₂)ᵀ i j * Fmat ζ j k =
      ((ζ⁻¹) ^ (i : ℕ) * ζ ^ (k : ℕ)) ^ (j : ℕ) := by
    intro j
    simp only [transpose_apply, Matrix.map_apply, Fmat, of_apply, hFr]
    rw [pow_right_comm, hζQ, mul_pow, ← pow_mul, ← pow_mul, mul_comm (i : ℕ) (j : ℕ),
      mul_comm (k : ℕ) (j : ℕ)]
  have hr5 : ((ζ⁻¹) ^ (i : ℕ) * ζ ^ (k : ℕ)) ^ 5 = 1 := by
    have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
    have hinv5 : ζ⁻¹ ^ 5 = 1 := by rw [inv_pow, h5, inv_one]
    rw [mul_pow, pow_right_comm ζ⁻¹ (i : ℕ) 5, pow_right_comm ζ (k : ℕ) 5, hinv5, h5, one_pow,
      one_pow, one_mul]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  by_cases hik : i = k
  · subst hik
    have : (ζ⁻¹) ^ (i : ℕ) * ζ ^ (i : ℕ) = 1 := by
      rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero _ hne)
    rw [sum_pow_five_eq_one this]
    simp
  · have hr1 : (ζ⁻¹) ^ (i : ℕ) * ζ ^ (k : ℕ) ≠ 1 := by
      intro h
      have h' := eq_inv_of_mul_eq_one_right h
      have h'' : ζ ^ (k : ℕ) = ζ ^ (i : ℕ) := by simpa [inv_pow] using h'
      exact hik (Fin.ext (hζ.pow_inj k.2 i.2 h'').symm)
    rw [sum_pow_five_eq_zero hr5 hr1]
    simp [hik]

theorem Pmat_mul_Fmat {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    Pmat L * Fmat ζ = Fmat ζ * diagonal (fun j : Fin 5 => ζ ^ (j : ℕ)) := by
  ext i j
  rw [mul_diagonal, Matrix.mul_apply]
  simp only [Pmat_apply, Fmat, of_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  have hi : ((finRotate 5 i : Fin 5) : ℕ) = ((i : ℕ) + 1) % 5 := by fin_cases i <;> rfl
  have h5 := hζ.pow_eq_one
  rw [hi, ← pow_add, ← Nat.succ_mul]
  have hmod : (((i : ℕ) + 1) % 5 * (j : ℕ)) % 5 = (((i : ℕ) + 1) * (j : ℕ)) % 5 := by
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  rw [pow_eq_pow_mod _ h5, hmod, ← pow_eq_pow_mod _ h5]

def tauVec (d : Fin 5 → L) : Fin 5 → L :=
  ![1, (d 0)⁻¹, (d 0 * d 1)⁻¹, (d 0 * d 1 * d 2)⁻¹, (d 0 * d 1 * d 2 * d 3)⁻¹]

theorem tauVec_step {d : Fin 5 → L} (hd0 : ∀ i, d i ≠ 0) (hprod : ∏ i, d i = 1) (i : Fin 5) :
    d i * tauVec d (finRotate 5 i) = tauVec d i := by
  have hp : d 0 * d 1 * d 2 * d 3 * d 4 = 1 := by rwa [Fin.prod_univ_five] at hprod
  have h0 := hd0 0
  have h1 := hd0 1
  have h2 := hd0 2
  have h3 := hd0 3
  have h4 := hd0 4
  fin_cases i
  · simp [tauVec, h0]
  · simp [tauVec]
    field_simp
  · simp [tauVec]
    field_simp
  · simp [tauVec]
    field_simp
  · simp [tauVec]
    field_simp
    linear_combination hp

theorem tauVec_pow {d : Fin 5 → L} {Q : ℕ} (hd : ∀ i, d i ^ (Q + 1) = 1) (i : Fin 5) :
    tauVec d i ^ (Q + 1) = 1 := by
  fin_cases i <;> simp [tauVec, inv_pow, mul_pow, hd]

theorem exists_conj_P [CharP L 2] (hFr : ∀ x, Fr₂ x = x ^ Q) {ζ : L}
    (hζ : IsPrimitiveRoot ζ 5) (hQ5 : 5 ∣ Q + 1) {a : SL5 L} (ha : a ∈ Dgrp L Q) :
    ∃ w ∈ U Fr₂, ∃ l ∈ Dgrp L Q, a * P L * w = w * l := by
  obtain ⟨d, hd, had⟩ := ha
  have hζQ1 : ζ ^ (Q + 1) = 1 := by
    obtain ⟨m, hm⟩ := hQ5
    rw [hm, pow_mul, hζ.pow_eq_one, one_pow]
  have hne : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζQ : ζ ^ Q = ζ⁻¹ := by
    rw [pow_succ] at hζQ1
    exact eq_inv_of_mul_eq_one_left hζQ1
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i
    rw [h, zero_pow (Nat.succ_ne_zero Q)] at this
    exact zero_ne_one this
  have hprod : ∏ i, d i = 1 := by
    have := a.2
    rw [had, det_diagonal] at this
    exact this
  have hDτ : ((diagonal (tauVec d)).map Fr₂)ᵀ * diagonal (tauVec d) = 1 :=
    diagonal_unitary hFr (tauVec_pow hd)
  have hF : ((Fmat ζ).map Fr₂)ᵀ * Fmat ζ = 1 := Fmat_unitary hFr hζ hζQ
  have hW0 : ((diagonal (tauVec d) * Fmat ζ).map Fr₂)ᵀ * (diagonal (tauVec d) * Fmat ζ) = 1 :=
    unitary_mul hDτ hF
  have hdet0 : (diagonal (tauVec d) * Fmat ζ).det ^ (Q + 1) = 1 := det_pow_of_unitary hFr hW0
  have hdet0ne : (diagonal (tauVec d) * Fmat ζ).det ≠ 0 := by
    intro h; rw [h, zero_pow (Nat.succ_ne_zero Q)] at hdet0; exact zero_ne_one hdet0
  set δ : L := ((diagonal (tauVec d) * Fmat ζ).det)⁻¹ with hδ
  have hδQ : δ ^ (Q + 1) = 1 := by rw [hδ, inv_pow, hdet0, inv_one]
  set D2 : Matrix (Fin 5) (Fin 5) L := diagonal (fun i : Fin 5 => if i = 0 then δ else 1) with hD2
  have hD2u : (D2.map Fr₂)ᵀ * D2 = 1 := diagonal_unitary hFr (fun i => by
    by_cases hi : i = 0
    · simp [hi, hδQ]
    · simp [hi])
  have hdet2 : D2.det = δ := by
    rw [hD2, det_diagonal, Fin.prod_univ_five]; simp
  set W : Matrix (Fin 5) (Fin 5) L := (diagonal (tauVec d) * Fmat ζ) * D2 with hW
  have hWdet : W.det = 1 := by
    rw [hW, det_mul, hdet2, hδ]; exact mul_inv_cancel₀ hdet0ne
  have hWU : (W.map Fr₂)ᵀ * W = 1 := unitary_mul hW0 hD2u
  set c : Fin 5 → L := fun j => ζ ^ (j : ℕ) with hc
  have hcdet : (diagonal c).det = 1 := by
    rw [det_diagonal, hc]
    simp only
    rw [Finset.prod_pow_eq_pow_sum]
    have : ∑ i : Fin 5, (i : ℕ) = 10 := by decide
    rw [this, show 10 = 5 * 2 from rfl, pow_mul, hζ.pow_eq_one, one_pow]
  have hlD : (⟨diagonal c, hcdet⟩ : SL5 L) ∈ Dgrp L Q :=
    ⟨c, fun j => by rw [hc]; simp only; rw [pow_right_comm, hζQ1, one_pow], rfl⟩
  refine ⟨⟨W, hWdet⟩, ?_, ⟨diagonal c, hcdet⟩, hlD, ?_⟩
  · exact (mem_U_iff Fr₂).2 hWU
  · apply Subtype.ext
    show (a : Matrix (Fin 5) (Fin 5) L) * Pmat L * W = W * diagonal c
    rw [had, hW]
    calc diagonal d * Pmat L * (diagonal (tauVec d) * Fmat ζ * D2)
        = diagonal d * (Pmat L * diagonal (tauVec d)) * Fmat ζ * D2 := by
          simp only [Matrix.mul_assoc]
      _ = diagonal d * (diagonal (fun i => tauVec d (finRotate 5 i)) * Pmat L) * Fmat ζ * D2 := by
          rw [Pmat_mul_diagonal]
      _ = diagonal (tauVec d) * Pmat L * Fmat ζ * D2 := by
          have hdiag : diagonal d * diagonal (fun i => tauVec d (finRotate 5 i)) =
              diagonal (tauVec d) := by
            rw [diagonal_mul_diagonal]
            congr 1
            funext i
            exact tauVec_step hd0 hprod i
          rw [← Matrix.mul_assoc (diagonal d), hdiag]
      _ = diagonal (tauVec d) * (Fmat ζ * diagonal c) * D2 := by
          rw [Matrix.mul_assoc (diagonal (tauVec d)), Pmat_mul_Fmat hζ]
      _ = diagonal (tauVec d) * Fmat ζ * (diagonal c * D2) := by
          simp only [Matrix.mul_assoc]
      _ = diagonal (tauVec d) * Fmat ζ * (D2 * diagonal c) := by
          rw [hD2, diagonal_mul_diagonal, diagonal_mul_diagonal]
          congr 2
          funext i
          exact mul_comm _ _
      _ = diagonal (tauVec d) * Fmat ζ * D2 * diagonal c := by
          simp only [Matrix.mul_assoc]

theorem conj_into_Dgrp_of_pow {x : SL5 L} (hx : x ^ 5 = 1) {m k : ℕ} (hmk : (m * k) % 5 = 1)
    {w l : SL5 L} (h : x ^ m * w = w * l) (hl : l ∈ Dgrp L Q) : w⁻¹ * x * w ∈ Dgrp L Q := by
  have h1 : x = (x ^ m) ^ k := by
    rw [← pow_mul, pow_eq_pow_mod _ hx, hmk, pow_one]
  have h2 : x ^ m = w * l * w⁻¹ := by
    rw [← h, mul_inv_cancel_right]
  have h3 : w⁻¹ * x * w = l ^ k := by
    calc w⁻¹ * x * w = w⁻¹ * (w * l * w⁻¹) ^ k * w := by rw [← h2, ← h1]
      _ = l ^ k := by rw [conj_pow]; group
  rw [h3]
  exact (Dgrp L Q).pow_mem hl k

theorem exists_conj_into_Dgrp [CharP L 2] (hFr : ∀ x, Fr₂ x = x ^ Q) {ζ : L}
    (hζ : IsPrimitiveRoot ζ 5) (hQ5 : 5 ∣ Q + 1) (z : Mon L Q) (hz : monHom z ^ 5 = 1) :
    ∃ u ∈ U Fr₂, u * monHom z * u⁻¹ ∈ Dgrp L Q := by
  classical
  have hfin : IsOfFinOrder (P L) := isOfFinOrder_iff_pow_eq_one.2 ⟨5, by norm_num, P_pow_five⟩
  obtain ⟨k, hk, hkz⟩ : ∃ k, k < 5 ∧ (P L) ^ k = (z.right : SL5 L) := by
    have h := hfin.mem_zpowers_iff_mem_range_orderOf.1 z.right.2
    rw [orderOf_P, Finset.mem_image] at h
    obtain ⟨k, hk, hkz⟩ := h
    exact ⟨k, Finset.mem_range.1 hk, hkz⟩
  by_cases hk0 : k = 0
  · subst hk0
    refine ⟨1, (U Fr₂).one_mem, ?_⟩
    rw [monHom_apply, ← hkz, pow_zero, mul_one, inv_one, one_mul, mul_one]
    exact z.left.2
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m * k) % 5 = 1 := by
      interval_cases k
      · exact absurd rfl hk0
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨4, rfl⟩
    have hzm : ((z ^ m).right : SL5 L) = P L := by
      have h1 : (z ^ m).right = z.right ^ m := map_pow SemidirectProduct.rightHom z m
      rw [h1, Subgroup.coe_pow, ← hkz, ← pow_mul, pow_eq_pow_mod _ P_pow_five, mul_comm, hm,
        pow_one]
    obtain ⟨w, hw, l, hl, hwl⟩ := exists_conj_P hFr hζ hQ5 (z ^ m).left.2
    have h2 : monHom z ^ m * w = w * l := by
      rw [← map_pow, monHom_apply, hzm]; exact hwl
    refine ⟨w⁻¹, (U Fr₂).inv_mem hw, ?_⟩
    rw [inv_inv]
    exact conj_into_Dgrp_of_pow hz hm h2 hl

end DFT

section Count

theorem mu_ne_zero {x : L} (hx : x ^ (Q + 1) = 1) : x ≠ 0 := by
  rintro rfl
  rw [zero_pow (Nat.succ_ne_zero Q)] at hx
  exact zero_ne_one hx

@[expose] def diagVec (e : Fin 4 → L) : Fin 5 → L :=
  ![e 0, e 1, e 2, e 3, (e 0 * e 1 * e 2 * e 3)⁻¹]

theorem diagVec_pow {e : Fin 4 → L} (he : ∀ i, e i ^ (Q + 1) = 1) (i : Fin 5) :
    diagVec e i ^ (Q + 1) = 1 := by
  fin_cases i <;> simp [diagVec, inv_pow, mul_pow, he]

theorem prod_diagVec {e : Fin 4 → L} (he : ∀ i, e i ≠ 0) : ∏ i, diagVec e i = 1 := by
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  rw [Fin.prod_univ_five]
  show e 0 * e 1 * e 2 * e 3 * (e 0 * e 1 * e 2 * e 3)⁻¹ = 1
  exact mul_inv_cancel₀ (by simp [h0, h1, h2, h3])

theorem Dgrp_diag_entry {A : SL5 L} (hA : A ∈ Dgrp L Q) (i : Fin 5) :
    (A : Matrix (Fin 5) (Fin 5) L) i i ^ (Q + 1) = 1 := by
  obtain ⟨d, hd, h⟩ := hA
  rw [h, diagonal_apply_eq]
  exact hd i

theorem card_Dgrp_eq (hmu : Nat.card {x : L // x ^ (Q + 1) = 1} = Q + 1) :
    Nat.card (Dgrp L Q) = (Q + 1) ^ 4 := by
  have e : Dgrp L Q ≃ (Fin 4 → {x : L // x ^ (Q + 1) = 1}) :=
    { toFun := fun A i =>
        ⟨(A.1 : Matrix (Fin 5) (Fin 5) L) i.castSucc i.castSucc, Dgrp_diag_entry A.2 _⟩
      invFun := fun e =>
        ⟨⟨diagonal (diagVec fun i => (e i).1), by
          rw [det_diagonal]; exact prod_diagVec (fun i => mu_ne_zero (e i).2)⟩,
          ⟨diagVec fun i => (e i).1, diagVec_pow (fun i => (e i).2), rfl⟩⟩
      left_inv := by
        rintro ⟨A, d, hd, hA⟩
        have hprod : ∏ i, d i = 1 := by
          have := A.2
          rw [hA, det_diagonal] at this
          exact this
        apply Subtype.ext
        apply Subtype.ext
        show diagonal (diagVec fun i : Fin 4 =>
          (A.1 : Matrix (Fin 5) (Fin 5) L) i.castSucc i.castSucc) = A.1
        rw [hA]
        congr 1
        funext i
        have hp : d 0 * d 1 * d 2 * d 3 * d 4 = 1 := by rwa [Fin.prod_univ_five] at hprod
        have h0 := mu_ne_zero (hd 0)
        have h1 := mu_ne_zero (hd 1)
        have h2 := mu_ne_zero (hd 2)
        have h3 := mu_ne_zero (hd 3)
        have h4 := mu_ne_zero (hd 4)
        fin_cases i
        · simp [diagVec]
        · simp [diagVec]
        · simp [diagVec]
        · simp [diagVec]
        · simp [diagVec]
          field_simp
          linear_combination -hp
      right_inv := by
        intro e
        funext i
        apply Subtype.ext
        fin_cases i <;> simp [diagVec] }
  rw [Nat.card_congr e, Nat.card_fun, hmu, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_mu [IsAlgClosed L] [CharP L 2] (hQ : ¬ 2 ∣ Q + 1) :
    Nat.card {x : L // x ^ (Q + 1) = 1} = Q + 1 := by
  have hm' : ((Q + 1 : ℕ) : L) ≠ 0 := fun h => hQ ((CharP.cast_eq_zero_iff L 2 (Q + 1)).1 h)
  have : NeZero (Q + 1) := ⟨Nat.succ_ne_zero Q⟩
  have : NeZero ((Q + 1 : ℕ) : L) := ⟨hm'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L (Q + 1)
  have h := hζ.card_rootsOfUnity
  have e : {x : L // x ^ (Q + 1) = 1} ≃ rootsOfUnity (Q + 1) L :=
    { toFun := fun x => ⟨Units.mk0 x.1 (mu_ne_zero x.2),
        (mem_rootsOfUnity (Q + 1) _).2 (Units.ext (by simpa using x.2))⟩
      invFun := fun u => ⟨u.1.1, by
        have := (mem_rootsOfUnity (Q + 1) u.1).1 u.2
        simpa using congrArg Units.val this⟩
      left_inv := fun x => rfl
      right_inv := fun u => by ext; rfl }
  rw [Nat.card_congr e]
  exact h

theorem card_Mon_eq [IsAlgClosed L] [CharP L 2] (hQ : ¬ 2 ∣ Q + 1) :
    Nat.card (Mon L Q) = (Q + 1) ^ 4 * 5 := by
  rw [card_Mon, card_Dgrp_eq (card_mu hQ)]

theorem finite_Mon [IsAlgClosed L] [CharP L 2] (hQ : ¬ 2 ∣ Q + 1) : Finite (Mon L Q) :=
  Nat.finite_of_card_ne_zero (by rw [card_Mon_eq hQ]; positivity)

theorem finite_roots (m : ℕ) (hm : 1 < m) : Finite {x : L // x ^ m = x} := by
  have hp : (Polynomial.X ^ m - Polynomial.X : Polynomial L) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L hm
  have h := Polynomial.finite_setOfPred_isRoot hp
  refine Set.Finite.to_subtype (h.subset ?_)
  intro x hx
  have hx' : x ^ m = x := hx
  show (Polynomial.X ^ m - Polynomial.X : Polynomial L).IsRoot x
  simp [Polynomial.IsRoot, hx']

theorem entry_pow_of_mem_U (hFr : ∀ x, Fr₂ x = x ^ Q) {A : SL5 L} (hA : A ∈ U Fr₂)
    (i j : Fin 5) : ((A : Matrix (Fin 5) (Fin 5) L) i j) ^ (Q * Q) =
      (A : Matrix (Fin 5) (Fin 5) L) i j := by
  have h := congrArg (fun X : SL5 L => (X : Matrix (Fin 5) (Fin 5) L) i j)
    (map_comp_of_mem_U Fr₂ hA)
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    RingHom.comp_apply, hFr] at h
  rw [← pow_mul] at h
  exact h

theorem finite_U (hFr : ∀ x, Fr₂ x = x ^ Q) (hQ : 2 ≤ Q) : Finite (U Fr₂) := by
  have hm : 1 < Q * Q := by nlinarith
  have := finite_roots (L := L) (Q * Q) hm
  refine Finite.of_injective
    (fun (A : U Fr₂) (i j : Fin 5) => (⟨(A.1 : Matrix (Fin 5) (Fin 5) L) i j,
      entry_pow_of_mem_U hFr A.2 i j⟩ : {x : L // x ^ (Q * Q) = x})) ?_
  intro A B h
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h i) j
  exact congrArg Subtype.val this

theorem exists_primitiveRoot_five [IsAlgClosed L] [CharP L 2] : ∃ ζ : L, IsPrimitiveRoot ζ 5 := by
  have h5 : ((5 : ℕ) : L) ≠ 0 := fun h => by
    have := (CharP.cast_eq_zero_iff L 2 5).1 h
    omega
  have : NeZero ((5 : ℕ) : L) := ⟨h5⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot L 5

end Count

end Unitary

end CFSG.RankThree.PartOne.KC1

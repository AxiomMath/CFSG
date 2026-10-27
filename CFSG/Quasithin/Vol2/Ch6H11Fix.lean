module

public import CFSG.Quasithin.Vol2.Ch6H11Norm
public import CFSG.Quasithin.Vol2.Ch9H11Fix

public section

noncomputable section

namespace CFSG.Quasithin.H13.H11M

open CFSG.Quasithin (fixV mem_fixV rk rkIdx frobPow hermSub)
open CFSG.Quasithin.JonesParshall (hermA mem_hermA sig sig_apply frobPow_eq_map hermA_apply
  frobPow_mul frobPow_transpose frobPow_frobPow twist_mem)
open CFSG.Quasithin.H13.H11P (Mat uu dd ww ul coe_uu coe_dd coe_ww coe_ul coe_inv_mul
  coe_mul_inv eq_one_of_sq_eq_one Uu card_Uu)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂ slFieldAut slFieldAut_apply)
open scoped Matrix

variable {F : Type} [Field F] [CharP F 2] {a : ℕ} (hσ : SigInv a F)

@[expose] def sigE : F ≃+* F :=
  { sig a with
    invFun := sig a
    left_inv := hσ
    right_inv := hσ }

theorem sigE_apply (x : F) : sigE hσ x = sig a x := rfl

theorem sigE_mul_self : sigE hσ * sigE hσ = 1 := RingEquiv.ext fun x => hσ x

theorem mapMatrix_sigE (X : Mat F) : (sigE hσ).mapMatrix X = frobPow a X := by
  rw [frobPow_eq_map]
  rfl

include hσ in
theorem sigE_ne_one {θ : F} (hθ : sig a θ ≠ θ) : sigE hσ ≠ 1 := fun h =>
  hθ (by rw [← sigE_apply hσ, h]; rfl)

abbrev sigH : MulAut (VH a F) := fA (sigE hσ)

theorem hm_sigH (v : VH a F) : hm (sigH hσ v) = frobPow a (hm v) := by
  rw [hm_fA, mapMatrix_sigE]

theorem conj_of_form {x : MulAut (VH a F)} {c : F} {M : SL₂ F} {τ : F ≃+* F}
    (hx : ∀ v, hm (x v) = c • ((M : Mat F) * τ.mapMatrix (hm v) * (frobPow a (M : Mat F))ᵀ))
    (g : SL₂ F) : x * rhoH hσ g * x⁻¹ = rhoH hσ (M * slFieldAut F τ g * M⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine MulEquiv.ext fun v => hm_injective ?_
  show hm (x (rhoH hσ g v)) = hm (rhoH hσ (M * slFieldAut F τ g * M⁻¹) (x v))
  rw [hx, hm_rhoH, hm_rhoH, hx, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, H11P.coe_slFieldAut, map_mul,
    frobPow_mul, Matrix.transpose_mul, H11P.mapMatrix_transpose, frobPow_mapMatrix]
  have h1 : ((M⁻¹ : SL₂ F) : Mat F) * (M : Mat F) = 1 := coe_inv_mul M
  have h2 : (frobPow a (M : Mat F))ᵀ * (frobPow a ((M⁻¹ : SL₂ F) : Mat F))ᵀ = 1 :=
    frobPow_mul_inv M
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((M⁻¹ : SL₂ F) : Mat F) (M : Mat F), h1, Matrix.one_mul,
    ← Matrix.mul_assoc (frobPow a (M : Mat F))ᵀ, h2, Matrix.one_mul]

omit [CharP F 2] in
theorem mapMatrix_mul (τ ψ : F ≃+* F) (X : Mat F) :
    (τ * ψ).mapMatrix X = τ.mapMatrix (ψ.mapMatrix X) := by
  ext i j
  rfl

omit [CharP F 2] in
theorem mapMatrix_one (X : Mat F) : (1 : F ≃+* F).mapMatrix X = X := by
  ext i j
  rfl

theorem sq_of_form {x : MulAut (VH a F)} {c : F} {M : SL₂ F} {τ : F ≃+* F}
    (hx : ∀ v, hm (x v) = c • ((M : Mat F) * τ.mapMatrix (hm v) * (frobPow a (M : Mat F))ᵀ))
    (v : VH a F) :
    hm (x (x v)) = (c * τ c) • (((M * slFieldAut F τ M : SL₂ F) : Mat F) *
      (τ * τ).mapMatrix (hm v) * (frobPow a ((M * slFieldAut F τ M : SL₂ F) : Mat F))ᵀ) := by
  rw [hx, hx, H11P.mapMatrix_smul, map_mul, map_mul, H11P.mapMatrix_transpose, ← frobPow_mapMatrix,
    Matrix.mul_smul, Matrix.smul_mul, smul_smul, mapMatrix_mul]
  congr 1
  simp only [Matrix.SpecialLinearGroup.coe_mul, H11P.coe_slFieldAut, frobPow_mul,
    Matrix.transpose_mul, Matrix.mul_assoc]

abbrev Zy (a : ℕ) (y : F) : Mat F := !![0, y; sig a y, 0]

include hσ in
theorem Zy_mem (y : F) : Zy a y ∈ hermA a F :=
  mem_hermA_lit hσ (w := (0 : F)) (z := 0) (map_zero _) (map_zero _)

include hσ in
theorem eq_one_of_form_eq_id {c : F} {P : Mat F} {ψ : F ≃+* F}
    (h : ∀ X ∈ hermA a F, c • (P * ψ.mapMatrix X * (frobPow a P)ᵀ) = X) : ψ = 1 := by
  have h1 := h _ (E11_mem hσ)
  have h2 := h _ (E22_mem hσ)
  have e100 := congrFun (congrFun h1 0) 0
  have e111 := congrFun (congrFun h1 1) 1
  have e200 := congrFun (congrFun h2 0) 0
  simp only [Matrix.smul_apply, twist_apply, RingEquiv.mapMatrix_apply, Matrix.map_apply,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, map_one, map_zero, smul_eq_mul] at e100 e111 e200
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_mul] at e100
    exact zero_ne_one e100
  have hP10 : P 1 0 = 0 := nsig_eq_zero (by
    have : c * (P 1 0 * sig a (P 1 0)) = 0 := by linear_combination e111
    exact (mul_eq_zero.mp this).resolve_left hc)
  have hP01 : P 0 1 = 0 := nsig_eq_zero (by
    have : c * (P 0 1 * sig a (P 0 1)) = 0 := by linear_combination e200
    exact (mul_eq_zero.mp this).resolve_left hc)
  have hZ : ∀ y : F, c * P 0 0 * sig a (P 1 1) * ψ y = y := by
    intro y
    have e := congrFun (congrFun (h _ (Zy_mem hσ y)) 0) 1
    simp only [Matrix.smul_apply, twist_apply, RingEquiv.mapMatrix_apply, Matrix.map_apply,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, map_zero, smul_eq_mul, hP10, hP01] at e
    linear_combination e
  have h11 := hZ 1
  rw [map_one, mul_one] at h11
  refine RingEquiv.ext fun y => ?_
  have := hZ y
  rw [h11, one_mul] at this
  exact this

@[expose] def FormS (x : MulAut (VH a F)) (M : SL₂ F) : Prop :=
  (M : Mat F) * frobPow a (M : Mat F) = 1 ∧
    ∀ v, hm (x v) = (M : Mat F) * frobPow a (hm v) * (frobPow a (M : Mat F))ᵀ

include hσ in
theorem mem_LH_or_formS [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {θ₀ : F} (hθ₀ : sig a θ₀ ≠ θ₀) {x : MulAut (VH a F)}
    (hx : x ∈ Subgroup.normalizer ((LH hσ : Subgroup (MulAut (VH a F))) : Set _))
    (hxx : x * x = 1) : x ∈ LH hσ ∨ ∃ M : SL₂ F, FormS x M := by
  obtain ⟨c, hcK, -, M, τ, hform⟩ := normal_form hσ ha hF hθ₀ hx
  have hid : ∀ X ∈ hermA a F, (c * τ c) • (((M * slFieldAut F τ M : SL₂ F) : Mat F) *
      (τ * τ).mapMatrix X * (frobPow a ((M * slFieldAut F τ M : SL₂ F) : Mat F))ᵀ) = X := by
    intro X hX
    have h := sq_of_form hform (mkH X hX)
    rw [← MulAut.mul_apply, hxx] at h
    exact h.symm
  have hττ : τ * τ = 1 := eq_one_of_form_eq_id hσ hid
  have hFn : Nat.card F = 2 ^ (2 * a) := by rw [Nat.card_eq_fintype_card, hF]
  have hτ : τ = 1 ∨ τ = sigE hσ := by
    by_cases hτ1 : τ = 1
    · exact Or.inl hτ1
    · exact Or.inr (H11P.ringAut_invol_unique hFn hτ1 (sigE_ne_one hσ hθ₀) hττ
        (sigE_mul_self hσ))
  have hτc : τ c = c := by
    rcases hτ with rfl | rfl
    · rfl
    · rw [sigE_apply, hcK]
  rw [hττ, hτc] at hid
  have hcc : c * c ≠ 0 := by
    intro h0
    have := hid _ (E11_mem hσ)
    rw [h0, zero_smul] at this
    have h4 : (0 : Mat F) 0 0 = (E11 F) 0 0 := congrFun (congrFun this 0) 0
    simp at h4
  obtain ⟨hP, hl⟩ := eq_one_of_twist_eq_smul hσ (g := M * slFieldAut F τ M) (l := (c * c)⁻¹)
    fun X hX => by
      conv_rhs => rw [← hid X hX]
      rw [mapMatrix_one, smul_smul, inv_mul_cancel₀ hcc, one_smul]
  have hc1 : c = 1 := H11P.eq_one_of_sq_eq_one (by rw [sq]; exact inv_eq_one.mp hl)
  subst hc1
  rcases hτ with rfl | rfl
  · left
    refine ⟨M, MulEquiv.ext fun v => hm_injective ?_⟩
    rw [hm_rhoH, hform, mapMatrix_one, one_smul]
  · right
    refine ⟨M, ?_, fun v => by rw [hform, one_smul, mapMatrix_sigE]⟩
    have := congrArg (fun g : SL₂ F => (g : Mat F)) hP
    simp only [Matrix.SpecialLinearGroup.coe_mul, H11P.coe_slFieldAut,
      Matrix.SpecialLinearGroup.coe_one] at this
    rwa [mapMatrix_sigE] at this

include hσ in
theorem mul_mem_LH_of_formS {x y : MulAut (VH a F)} {M M' : SL₂ F} (hx : FormS x M)
    (hy : FormS y M') : x * y ∈ LH hσ := by
  refine ⟨M * slFieldAut F (sigE hσ) M', MulEquiv.ext fun v => hm_injective ?_⟩
  show hm (rhoH hσ (M * slFieldAut F (sigE hσ) M') v) = hm (x (y v))
  rw [hm_rhoH, hx.2, hy.2]
  simp only [Matrix.SpecialLinearGroup.coe_mul, H11P.coe_slFieldAut, mapMatrix_sigE, frobPow_mul,
    Matrix.transpose_mul, frobPow_transpose, JonesParshall.frobPow_frobPow a hσ, Matrix.mul_assoc]

theorem frobPow_smul (l : F) (X : Mat F) : frobPow a (l • X) = sig a l • frobPow a X := by
  ext i j
  simp only [frobPow_apply, Matrix.smul_apply, smul_eq_mul, mul_pow, sig_apply]

theorem frobPow_add (X Y : Mat F) : frobPow a (X + Y) = frobPow a X + frobPow a Y := by
  ext i j
  simp only [frobPow_apply, Matrix.add_apply]
  exact add_pow_char_pow _ _ 2 a

theorem det_frobPow (X : Mat F) : (frobPow a X).det = sig a X.det := by
  rw [frobPow_eq_map]
  exact (RingHom.map_det (sig a) X).symm

theorem det_hilb (θ : F) (M : SL₂ F) :
    (θ • (1 : Mat F) + sig a θ • (M : Mat F)).det =
      θ ^ 2 + θ * sig a θ * ((M : Mat F) 0 0 + (M : Mat F) 1 1) + sig a θ ^ 2 := by
  have hM : (M : Mat F).det = 1 := M.2
  have e : ∀ i j : Fin 2, (θ • (1 : Mat F) + sig a θ • (M : Mat F)) i j =
      θ * (1 : Mat F) i j + sig a θ * (M : Mat F) i j := fun i j => rfl
  rw [Matrix.det_fin_two] at hM ⊢
  rw [e, e, e, e]
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  linear_combination sig a θ ^ 2 * hM

include hσ in
theorem exists_hilbert90 [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a))
    {θ₀ : F} (hθ₀ : sig a θ₀ ≠ θ₀) {M : SL₂ F} (hM : (M : Mat F) * frobPow a (M : Mat F) = 1) :
    ∃ N : SL₂ F, (M : Mat F) * frobPow a (N : Mat F) = (N : Mat F) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨θ, hd⟩ : ∃ θ : F, (θ • (1 : Mat F) + sig a θ • (M : Mat F)).det ≠ 0 := by
    by_cases htr : (M : Mat F) 0 0 + (M : Mat F) 1 1 = 0
    · refine ⟨θ₀, ?_⟩
      rw [det_hilb, htr, mul_zero, add_zero]
      intro h0
      have h3 : (θ₀ + sig a θ₀) ^ 2 = 0 := by linear_combination h0 + θ₀ * sig a θ₀ * h2
      have h4 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h3
      exact hθ₀ (by linear_combination h4 - θ₀ * h2)
    · refine ⟨1, ?_⟩
      rw [det_hilb, sig_one]
      intro h0
      exact htr (by linear_combination h0 - h2)
  set P := θ • (1 : Mat F) + sig a θ • (M : Mat F) with hPdef
  have hMP : (M : Mat F) * frobPow a P = P := by
    rw [hPdef, frobPow_add, frobPow_smul, frobPow_smul, frobPow_one, hσ, Matrix.mul_add,
      Matrix.mul_smul, Matrix.mul_smul, hM, Matrix.mul_one, add_comm]
  have hdK : sig a P.det = P.det := by
    have h3 := congrArg Matrix.det hMP
    rw [Matrix.det_mul, M.2, one_mul, det_frobPow] at h3
    exact h3
  set d := P.det with hddef
  set l : F := d⁻¹ ^ (2 ^ (2 * a - 1)) with hldef
  have hl2 : l ^ 2 * d = 1 := by
    have e : l ^ 2 = d⁻¹ := by
      rw [hldef, ← pow_mul, show 2 ^ (2 * a - 1) * 2 = Fintype.card F by
        rw [hF, ← pow_succ]
        congr 1
        omega, FiniteField.pow_card]
    rw [e, inv_mul_cancel₀ hd]
  have hlK : sig a l = l := by rw [hldef, map_pow, map_inv₀, hdK]
  refine ⟨⟨l • P, ?_⟩, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin]
    exact hl2
  · show (M : Mat F) * frobPow a (l • P) = l • P
    rw [frobPow_smul, hlK, Matrix.mul_smul, hMP]

include hσ in
theorem formS_conj {x : MulAut (VH a F)} {M N : SL₂ F} (hx : FormS x M)
    (hN : (M : Mat F) * frobPow a (N : Mat F) = N) :
    x * rhoH hσ N = rhoH hσ N * sigH hσ := by
  have hN' : frobPow a (M : Mat F) * (N : Mat F) = frobPow a (N : Mat F) := by
    have h3 := congrArg (frobPow a) hN
    rwa [frobPow_mul, JonesParshall.frobPow_frobPow a hσ] at h3
  refine MulEquiv.ext fun v => hm_injective ?_
  show hm (x (rhoH hσ N v)) = hm (rhoH hσ N (sigH hσ v))
  rw [hx.2, hm_rhoH, hm_rhoH, hm_sigH, frobPow_mul, frobPow_mul, frobPow_transpose,
    JonesParshall.frobPow_frobPow a hσ]
  calc (M : Mat F) * (frobPow a (N : Mat F) * frobPow a (hm v) * (N : Mat F)ᵀ) *
        (frobPow a (M : Mat F))ᵀ =
      ((M : Mat F) * frobPow a (N : Mat F)) * frobPow a (hm v) *
        (frobPow a (M : Mat F) * (N : Mat F))ᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
    _ = (N : Mat F) * frobPow a (hm v) * (frobPow a (N : Mat F))ᵀ := by rw [hN, hN']

section Conj

variable {V : Type} [CommGroup V]

omit [CharP F 2] in
theorem mem_fixV_zpowers {x : MulAut V} {v : V} : v ∈ fixV (Subgroup.zpowers x) ↔ x v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

omit [CharP F 2] in
theorem fixV_anti {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : fixV Y ≤ fixV X :=
  fun _ hv x hx => hv x (h hx)

abbrev conjSub (g : MulAut V) (A : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  A.map (MulAut.conj g).toMonoidHom

omit [CharP F 2] in
theorem card_conjSub (g : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card (conjSub g A) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

omit [CharP F 2] in
theorem card_fixV_conjSub (g : MulAut V) (A : Subgroup (MulAut V)) :
    Nat.card (fixV (conjSub g A)) = Nat.card (fixV A) :=
  CFSG.Quasithin.ConjTransport.card_fixV_map_conj A g

end Conj

abbrev KS (a : ℕ) (F : Type) [Field F] [CharP F 2] : Type := {k : F // sig a k = k}

theorem card_KS [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) :
    Nat.card (KS a F) = 2 ^ a := by
  rw [← CFSG.Quasithin.B45L2.card_frob_fixed ha hF]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun k => by rw [sig_apply])

theorem hm_ext {v w : VH a F} (h00 : hm v 0 0 = hm w 0 0) (h01 : hm v 0 1 = hm w 0 1)
    (h11 : hm v 1 1 = hm w 1 1) : v = w := by
  apply hm_injective
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · show hm v 1 0 = hm w 1 0
    rw [sig_offdiag (hm_mem v), sig_offdiag (hm_mem w), h01]
  · exact h11

include hσ in
theorem card_fix_sigH [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) :
    Nat.card (fixV (Subgroup.zpowers (sigH hσ))) = (2 ^ a) ^ 3 := by
  have hK := card_KS (a := a) (F := F) ha hF
  have h3 : Nat.card (KS a F × KS a F × KS a F) = (2 ^ a) ^ 3 := by
    rw [Nat.card_prod, Nat.card_prod, hK]
    ring
  have hmem : ∀ k : KS a F × KS a F × KS a F,
      !![(k.1 : F), (k.2.1 : F); (k.2.1 : F), (k.2.2 : F)] ∈ hermA a F := by
    intro k
    have h := mem_hermA_lit hσ (w := (k.1 : F)) (x := (k.2.1 : F)) (z := (k.2.2 : F)) k.1.2
      k.2.2.2
    rwa [k.2.1.2] at h
  have hfix : ∀ k, mkH _ (hmem k) ∈ fixV (Subgroup.zpowers (sigH hσ)) := by
    intro k
    rw [mem_fixV_zpowers]
    apply hm_injective
    have e1 := k.1.2
    have e2 := k.2.1.2
    have e3 := k.2.2.2
    rw [sig_apply] at e1 e2 e3
    rw [hm_sigH, hm_mkH, frobPow_lit, e1, e2, e3]
  apply le_antisymm
  · rw [← h3]
    refine Nat.card_le_card_of_injective (fun v => (⟨hm v.1 0 0, sig_diag (hm_mem _) 0⟩,
      ⟨hm v.1 0 1, ?_⟩, ⟨hm v.1 1 1, sig_diag (hm_mem _) 1⟩)) ?_
    · have h := congrArg hm ((mem_fixV_zpowers (x := sigH hσ)).mp v.2)
      rw [hm_sigH] at h
      have e := congrFun (congrFun h 0) 1
      rwa [frobPow_apply, ← sig_apply] at e
    · intro v w hvw
      simp only [Prod.mk.injEq, Subtype.mk.injEq] at hvw
      exact Subtype.ext (hm_ext hvw.1 hvw.2.1 hvw.2.2)
  · rw [← h3]
    refine Nat.card_le_card_of_injective (fun k => ⟨mkH _ (hmem k), hfix k⟩) ?_
    intro k k' hkk
    have h := congrArg (fun v : fixV (Subgroup.zpowers (sigH hσ)) => hm v.1) hkk
    simp only [hm_mkH] at h
    have e00 := congrFun (congrFun h 0) 0
    have e01 := congrFun (congrFun h 0) 1
    have e11 := congrFun (congrFun h 1) 1
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e11
    exact Prod.ext (Subtype.ext e00) (Prod.ext (Subtype.ext e01) (Subtype.ext e11))

include hσ in
theorem card_fix_formS [Fintype F] (ha : 1 ≤ a) (hF : Fintype.card F = 2 ^ (2 * a)) {θ₀ : F}
    (hθ₀ : sig a θ₀ ≠ θ₀) {x : MulAut (VH a F)} {M : SL₂ F} (hx : FormS x M) :
    Nat.card (fixV (Subgroup.zpowers x)) = (2 ^ a) ^ 3 := by
  obtain ⟨N, hN⟩ := exists_hilbert90 hσ ha hF hθ₀ hx.1
  have hc := formS_conj hσ hx hN
  have hxe : x = rhoH hσ N * sigH hσ * (rhoH hσ N)⁻¹ := by
    rw [← hc, mul_inv_cancel_right]
  have hz : Subgroup.zpowers x = conjSub (rhoH hσ N) (Subgroup.zpowers (sigH hσ)) := by
    rw [conjSub, MonoidHom.map_zpowers, hxe]
    rfl
  rw [hz, card_fixV_conjSub, card_fix_sigH hσ ha hF]

end CFSG.Quasithin.H13.H11M

end

module

public import CFSG.Timmesfeld.Bridge.RootClosureL2Defs

public section

namespace CFSG.Timmesfeld.Bridge.RootClosure

open CFSG.Timmesfeld Matrix

namespace L2Torus

variable {F : Type*} [Field F]

@[expose] def slOver (R : Subring F) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) where
  carrier := {M : Matrix.SpecialLinearGroup (Fin 2) F |
    ∀ i j, (M : Matrix (Fin 2) (Fin 2) F) i j ∈ R}
  mul_mem' {M N} hM hN i j := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    exact R.sum_mem fun k _ => R.mul_mem (hM i k) (hN k j)
  one_mem' i j := by
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  inv_mem' {M} hM i j := by
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hM 1 1
    · exact R.neg_mem (hM 0 1)
    · exact R.neg_mem (hM 1 0)
    · exact hM 0 0

@[expose] def conjMat (P P' : Matrix (Fin 2) (Fin 2) F) (h : P * P' = 1) (h' : P' * P = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun M := ⟨P * M * P', by rw [det_mul, det_mul, M.2, mul_one, ← det_mul, h, det_one]⟩
  map_one' := Subtype.ext (by
    change P * 1 * P' = 1
    rw [mul_one, h])
  map_mul' M N := Subtype.ext (by
    change P * ((M : Matrix (Fin 2) (Fin 2) F) * N) * P' = P * M * P' * (P * N * P')
    rw [show P * M * P' * (P * N * P') = P * M * (P' * P) * N * P' by
      simp only [Matrix.mul_assoc], h', Matrix.mul_one]
    simp only [Matrix.mul_assoc])

theorem coe_conjMat (P P' : Matrix (Fin 2) (Fin 2) F) (h : P * P' = 1) (h' : P' * P = 1)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    (conjMat P P' h h' M : Matrix (Fin 2) (Fin 2) F) = P * M * P' := rfl

theorem trace_eq_one_of_pow_three [CharP F 2] {g : Matrix.SpecialLinearGroup (Fin 2) F}
    (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set A := (g : Matrix (Fin 2) (Fin 2) F) 0 0
  set B := (g : Matrix (Fin 2) (Fin 2) F) 0 1
  set C := (g : Matrix (Fin 2) (Fin 2) F) 1 0
  set D := (g : Matrix (Fin 2) (Fin 2) F) 1 1
  have hdet : A * D - B * C = 1 := by
    have := g.2
    rwa [det_fin_two] at this
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![A, B; C, D] := eta_fin_two _
  have h3' : (g : Matrix (Fin 2) (Fin 2) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, h3, Matrix.SpecialLinearGroup.coe_one]
  rw [hg, pow_succ, pow_two, mul_fin_two, mul_fin_two, Matrix.one_fin_two] at h3'
  have e00 := congrFun₂ h3' 0 0
  have e01 := congrFun₂ h3' 0 1
  have e10 := congrFun₂ h3' 1 0
  have e11 := congrFun₂ h3' 1 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    at e00 e01 e10 e11
  by_contra hτ
  have hk : (A + D - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 hτ)
  have f01 : (A + D - 1) ^ 2 * B = 0 := by
    linear_combination e01 + B * hdet - (A + D - 1) * B * h2
  have f10 : (A + D - 1) ^ 2 * C = 0 := by
    linear_combination e10 + C * hdet - (A + D - 1) * C * h2
  have f00 : (A + D - 1) ^ 2 * A = 1 + (A + D) := by
    linear_combination e00 + (2 * A + D) * hdet - (A + D - 1) * A * h2
  have f11 : (A + D - 1) ^ 2 * D = 1 + (A + D) := by
    linear_combination e11 + (A + 2 * D) * hdet - (A + D - 1) * D * h2
  have hB0 : B = 0 := (mul_eq_zero.1 f01).resolve_left hk
  have hC0 : C = 0 := (mul_eq_zero.1 f10).resolve_left hk
  have hτ0 : A + D = 0 := by
    have : (A + D - 1) ^ 2 * (A + D) = 0 := by
      linear_combination f00 + f11 + (1 + (A + D)) * h2
    exact (mul_eq_zero.1 this).resolve_left hk
  have hA1 : A = 1 := by
    have : (A + D - 1) ^ 2 = 1 := by
      rw [hτ0]
      ring
    rw [this, one_mul, hτ0, add_zero] at f00
    exact f00
  have hD1 : D = 1 := by linear_combination hτ0 - hA1 - h2
  apply h1
  ext i j
  fin_cases i <;> fin_cases j
  · exact hA1
  · exact hB0
  · exact hC0
  · exact hD1

theorem conj_upperElt_of_conj {h : Matrix.SpecialLinearGroup (Fin 2) F} {s β : F} (hβ : β ≠ 0)
    (hh : h * RankOne.upperElt F s * h⁻¹ = RankOne.upperElt F β) (t : F) :
    h * RankOne.upperElt F t * h⁻¹ =
      RankOne.upperElt F ((h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t) := by
  obtain ⟨A, B, C, D, hH⟩ : ∃ A B C D : F, (h : Matrix (Fin 2) (Fin 2) F) = !![A, B; C, D] :=
    ⟨_, _, _, _, eta_fin_two _⟩
  have hdet : A * D - B * C = 1 := by
    have := h.2
    rwa [hH, det_fin_two_of] at this
  have hh' : h * RankOne.upperElt F s = RankOne.upperElt F β * h := by
    rw [← hh, inv_mul_cancel_right]
  have e00 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
    (M : Matrix (Fin 2) (Fin 2) F) 0 0) hh'
  simp only [Matrix.SpecialLinearGroup.coe_mul, ARS.NaturalModule.coe_upperElt, hH,
    mul_fin_two, of_apply, cons_val', cons_val_zero, empty_val', cons_val_fin_one] at e00
  have hC : C = 0 := by
    have : β * C = 0 := by linear_combination -e00
    exact (mul_eq_zero.1 this).resolve_left hβ
  have hA : (h : Matrix (Fin 2) (Fin 2) F) 0 0 = A := by
    rw [hH]
    rfl
  rw [hA, mul_inv_eq_iff_eq_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, ARS.NaturalModule.coe_upperElt, hH]
  rw [mul_fin_two, mul_fin_two]
  fin_cases i <;> fin_cases j <;>
    simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (-A ^ 2 * t) * hC
  · linear_combination (-A * t) * hdet - A * t * B * hC
  · ring
  · linear_combination t * hC

@[expose] def multSubring (W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) : Subring F where
  carrier := {k | ∀ t, RankOne.upperElt F t ∈ W → RankOne.upperElt F (k * t) ∈ W}
  mul_mem' {k l} hk hl t ht := by
    rw [mul_assoc]
    exact hk _ (hl t ht)
  one_mem' t ht := by rwa [one_mul]
  add_mem' {k l} hk hl t ht := by
    rw [add_mul, ← RankOne.upperElt_mul]
    exact W.mul_mem (hk t ht) (hl t ht)
  zero_mem' t _ := by
    rw [zero_mul, RankOne.upperElt_zero]
    exact W.one_mem
  neg_mem' {k} hk t ht := by
    have : RankOne.upperElt F (-k * t) = (RankOne.upperElt F (k * t))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, RankOne.upperElt_mul, neg_mul, neg_add_cancel,
        RankOne.upperElt_zero]
    rw [this]
    exact W.inv_mem (hk t ht)

end L2Torus

open L2Torus in
theorem l2TorusIrredStmt : L2TorusIrredStmt := by
  intro F _ _ _ _ x a b h ha hb ha1 hb1 _ hx hax hgen hh W hWU haW hWh
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  obtain ⟨s, rfl⟩ := (RankOne.mem_upperUnipotent_iff F).1 ha
  obtain ⟨β, rfl⟩ := (RankOne.mem_upperUnipotent_iff F).1 hb
  have hs : s ≠ 0 := by
    rintro rfl
    exact ha1 (RankOne.upperElt_zero F)
  have hβ : β ≠ 0 := by
    rintro rfl
    exact hb1 (RankOne.upperElt_zero F)
  set lam := (h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2
  have hconj : ∀ t, h * RankOne.upperElt F t * h⁻¹ = RankOne.upperElt F (lam * t) :=
    conj_upperElt_of_conj hβ hh
  have hβs : β = lam * s := RankOne.upperElt_injective F (hh.symm.trans (hconj s))
  obtain ⟨p, q, r, t', hX⟩ : ∃ p q r t' : F, (x : Matrix (Fin 2) (Fin 2) F) = !![p, q; r, t'] :=
    ⟨_, _, _, _, eta_fin_two _⟩
  have hdetx : p * t' - q * r = 1 := by
    have := x.2
    rwa [hX, det_fin_two_of] at this
  have hx' : (x : Matrix (Fin 2) (Fin 2) F) * x = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx, Matrix.SpecialLinearGroup.coe_one]
  rw [hX, mul_fin_two, one_fin_two] at hx'
  have e00 := congrFun₂ hx' 0 0
  have e11 := congrFun₂ hx' 1 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    at e00 e11
  have ht' : t' = p := by
    have hsq : (p + t') ^ 2 = 0 := by linear_combination e00 + e11 + 2 * hdetx + 2 * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
    linear_combination this - p * h2
  subst t'
  have hax3 : (RankOne.upperElt F s * x) ^ 3 = 1 := hax ▸ pow_orderOf_eq_one _
  have hax1 : RankOne.upperElt F s * x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hax
    exact absurd hax (by norm_num)
  have htr := trace_eq_one_of_pow_three hax3 hax1
  rw [Matrix.SpecialLinearGroup.coe_mul, ARS.NaturalModule.coe_upperElt, hX, mul_fin_two] at htr
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
    at htr
  have hsr : s * r = 1 := by linear_combination htr - p * h2
  have hr : r = s⁻¹ := (inv_eq_of_mul_eq_one_right hsr).symm
  subst hr
  have hq : q = s * (p ^ 2 - 1) := by
    have h1 : q * s⁻¹ = p ^ 2 - 1 := by linear_combination -hdetx
    calc q = q * s⁻¹ * s := by rw [inv_mul_cancel_right₀ hs]
      _ = s * (p ^ 2 - 1) := by rw [h1, mul_comm]
  subst hq
  have hss : s⁻¹ * s = 1 := inv_mul_cancel₀ hs
  have hPP' : !![s⁻¹, p + 1; 0, 1] * !![s, -(s * (p + 1)); 0, 1] =
      (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [mul_fin_two, one_fin_two]
    simp [hs]
  have hP'P : !![s, -(s * (p + 1)); 0, 1] * !![s⁻¹, p + 1; 0, 1] =
      (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [mul_fin_two, one_fin_two]
    simp [hs]
  set c := conjMat _ _ hPP' hP'P with hc
  have hcu : ∀ t, (c (RankOne.upperElt F t) : Matrix (Fin 2) (Fin 2) F) =
      !![1, s⁻¹ * t; 0, 1] := by
    intro t
    rw [hc, coe_conjMat, ARS.NaturalModule.coe_upperElt, mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · linear_combination hss
    · linear_combination -(p + 1) * hss
    · ring
    · ring
  have hcx : (c x : Matrix (Fin 2) (Fin 2) F) = !![1, 0; 1, 1] := by
    rw [hc, coe_conjMat, hX, mul_fin_two, mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
        Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · linear_combination (2 * p + 1) * hss + p * h2
    · linear_combination (-(2 * p + 1) * (p + 1) + (p ^ 2 - 1)) * hss - (p + 1) * h2
    · linear_combination hss
    · linear_combination -(p + 1) * hss - h2
  set R := Subring.closure ({lam} : Set F)
  have hS : ⊤ ≤ (slOver R).comap c := by
    rw [← hgen, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    · intro i j
      rw [hcx]
      fin_cases i <;> fin_cases j <;> simp [R.one_mem, R.zero_mem]
    · intro i j
      rw [hcu, hss]
      fin_cases i <;> fin_cases j <;> simp [R.one_mem, R.zero_mem]
    · intro i j
      rw [hcu, hβs, mul_comm lam s, inv_mul_cancel_left₀ hs]
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
        of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
      · exact R.one_mem
      · exact Subring.subset_closure (Set.mem_singleton lam)
      · exact R.zero_mem
      · exact R.one_mem
  have hRtop : ∀ y : F, y ∈ R := by
    intro y
    have h1 := hS (Subgroup.mem_top (RankOne.upperElt F (s * y))) 0 1
    rwa [hcu, inv_mul_cancel_left₀ hs] at h1
  have hT : R ≤ multSubring W :=
    Subring.closure_le.2 (Set.singleton_subset_iff.2 fun t ht => by
      rw [← hconj]
      exact hWh _ ht)
  refine le_antisymm hWU fun g hg => ?_
  obtain ⟨t, rfl⟩ := (RankOne.mem_upperUnipotent_iff F).1 hg
  have h1 := hT (hRtop (t * s⁻¹)) s haW
  rwa [mul_assoc, hss, mul_one] at h1

end CFSG.Timmesfeld.Bridge.RootClosure

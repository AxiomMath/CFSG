module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof174Host.U3

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix

variable {p f : ℕ} {K : Type} [Field K]

abbrev ie : HypIndex 1 1 := .inl 0
abbrev iw : HypIndex 1 1 := .inr (.inl 0)
abbrev jf : HypIndex 1 1 := .inr (.inr 0)

theorem idx_cases (a : HypIndex 1 1) : a = ie ∨ a = iw ∨ a = jf := by
  rcases a with i | i | i <;> fin_cases i <;> simp

theorem sum_hyp (g : HypIndex 1 1 → K) : ∑ a, g a = g ie + g iw + g jf := by
  simp [Fintype.sum_sum_type, add_assoc]

theorem vec_ext {v u : HypIndex 1 1 → K} (he : v ie = u ie) (hw : v iw = u iw)
    (hf : v jf = u jf) : v = u := by
  funext a
  rcases idx_cases a with rfl | rfl | rfl <;> assumption

theorem mat_ext {A B : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (h : ∀ a b, (a = ie ∨ a = iw ∨ a = jf) → (b = ie ∨ b = iw ∨ b = jf) → A a b = B a b) :
    A = B := by
  ext a b
  exact h a b (idx_cases a) (idx_cases b)

@[expose] def eqv3 : HypIndex 1 1 ≃ Fin 3 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

theorem det_hyp3 (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) :
    M.det = M ie ie * M iw iw * M jf jf - M ie ie * M iw jf * M jf iw
      - M ie iw * M iw ie * M jf jf + M ie iw * M iw jf * M jf ie
      + M ie jf * M iw ie * M jf iw - M ie jf * M iw iw * M jf ie := by
  rw [← Matrix.det_reindex_self eqv3 M, Matrix.det_fin_three]
  rfl

theorem hypForm_eq (h : UnitaryFieldData p f K) (x y : HypIndex 1 1 → K) :
    hypForm h 1 1 x y = h.bar (x ie) * y jf + h.bar (x iw) * y iw + h.bar (x jf) * y ie := by
  rw [hypForm_apply, sum_hyp]
  rfl

@[expose] def dg (a b d : K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  Matrix.diagonal (Sum.elim (fun _ => a) (Sum.elim (fun _ => b) (fun _ => d)))

@[simp] theorem dg_ee (a b d : K) : dg a b d ie ie = a := by simp [dg]
@[simp] theorem dg_ww (a b d : K) : dg a b d iw iw = b := by simp [dg]
@[simp] theorem dg_ff (a b d : K) : dg a b d jf jf = d := by simp [dg]
@[simp] theorem dg_ew (a b d : K) : dg a b d ie iw = 0 := by simp [dg]
@[simp] theorem dg_ef (a b d : K) : dg a b d ie jf = 0 := by simp [dg]
@[simp] theorem dg_we (a b d : K) : dg a b d iw ie = 0 := by simp [dg]
@[simp] theorem dg_wf (a b d : K) : dg a b d iw jf = 0 := by simp [dg]
@[simp] theorem dg_fe (a b d : K) : dg a b d jf ie = 0 := by simp [dg]
@[simp] theorem dg_fw (a b d : K) : dg a b d jf iw = 0 := by simp [dg]

theorem dg_mul (a b d a' b' d' : K) : dg a b d * dg a' b' d' = dg (a * a') (b * b') (d * d') := by
  rw [dg, dg, dg, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  rcases x with i | i | i <;> rfl

theorem det_dg (a b d : K) : (dg a b d).det = a * b * d := by
  rw [det_hyp3]
  simp

theorem dg_gram (h : UnitaryFieldData p f K) {a b d : K} (h1 : h.bar a * d = 1)
    (h2 : h.bar b * b = 1) :
    ((dg a b d).map h.bar)ᵀ * hypGram 1 1 K * dg a b d = hypGram 1 1 K := by
  have h1' : h.bar d * a = 1 := by
    have := congrArg h.bar h1
    rwa [map_mul, h.bar_bar, map_one, mul_comm] at this
  refine mat_ext fun i j hi hj => ?_
  rw [conjTranspose_hypGram_mul_apply, sum_hyp]
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    simp [hypGram_apply, h1, h2, h1']

@[expose] noncomputable def tauMat (h : UnitaryFieldData p f K) (x : Kˣ) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  dg (x : K) (h.bar x * (x : K)⁻¹) (h.bar x)⁻¹

theorem bar_ne_zero (h : UnitaryFieldData p f K) (x : Kˣ) : h.bar (x : K) ≠ 0 :=
  (map_ne_zero h.bar).mpr x.ne_zero

theorem tauMat_gram (h : UnitaryFieldData p f K) (x : Kˣ) :
    ((tauMat h x).map h.bar)ᵀ * hypGram 1 1 K * tauMat h x = hypGram 1 1 K := by
  refine dg_gram h (mul_inv_cancel₀ (bar_ne_zero h x)) ?_
  rw [map_mul, map_inv₀, h.bar_bar]
  field_simp [bar_ne_zero h x, x.ne_zero]

theorem det_tauMat (h : UnitaryFieldData p f K) (x : Kˣ) : (tauMat h x).det = 1 := by
  rw [tauMat, det_dg]
  field_simp [bar_ne_zero h x, x.ne_zero]

@[expose] noncomputable def tau (h : UnitaryFieldData p f K) : Kˣ →* hypSU h 1 1 where
  toFun x := mkHypSU h (tauMat h x) (tauMat_gram h x) (det_tauMat h x)
  map_one' := by
    refine Subtype.ext (Units.ext ?_)
    change tauMat h 1 = 1
    refine mat_ext fun i j hi hj => ?_
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp [tauMat]
  map_mul' x y := by
    refine Subtype.ext (Units.ext ?_)
    change tauMat h (x * y) = tauMat h x * tauMat h y
    rw [tauMat, tauMat, tauMat, dg_mul, Units.val_mul, map_mul]
    congr 1
    · field_simp [x.ne_zero, y.ne_zero]
    · rw [mul_inv]

theorem coe_tau (h : UnitaryFieldData p f K) (x : Kˣ) :
    (((tau h x : hypSU h 1 1) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      tauMat h x := rfl

theorem tau_injective (h : UnitaryFieldData p f K) : Function.Injective (tau h) := by
  intro x y hxy
  have := congrArg (fun g : hypSU h 1 1 =>
    ((g : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) ie ie) hxy
  simp only [coe_tau, tauMat, dg_ee] at this
  exact Units.ext this

theorem tau_comm (h : UnitaryFieldData p f K) (x y : Kˣ) : tau h x * tau h y = tau h y * tau h x := by
  rw [← map_mul, ← map_mul, mul_comm]

@[expose] def sMat : Matrix (HypIndex 1 1) (HypIndex 1 1) K :=
  Matrix.of fun a b => if a = hypPartner b then (if b = iw then -1 else 1) else 0

@[simp] theorem sMat_ee : (sMat : Matrix _ _ K) ie ie = 0 := by simp [sMat]
@[simp] theorem sMat_ew : (sMat : Matrix _ _ K) ie iw = 0 := by simp [sMat]
@[simp] theorem sMat_ef : (sMat : Matrix _ _ K) ie jf = 1 := by simp [sMat]
@[simp] theorem sMat_we : (sMat : Matrix _ _ K) iw ie = 0 := by simp [sMat]
@[simp] theorem sMat_ww : (sMat : Matrix _ _ K) iw iw = -1 := by simp [sMat]
@[simp] theorem sMat_wf : (sMat : Matrix _ _ K) iw jf = 0 := by simp [sMat]
@[simp] theorem sMat_fe : (sMat : Matrix _ _ K) jf ie = 1 := by simp [sMat]
@[simp] theorem sMat_fw : (sMat : Matrix _ _ K) jf iw = 0 := by simp [sMat]
@[simp] theorem sMat_ff : (sMat : Matrix _ _ K) jf jf = 0 := by simp [sMat]

theorem sMat_gram (h : UnitaryFieldData p f K) :
    ((sMat : Matrix _ _ K).map h.bar)ᵀ * hypGram 1 1 K * sMat = hypGram 1 1 K := by
  refine mat_ext fun i j hi hj => ?_
  rw [conjTranspose_hypGram_mul_apply, sum_hyp]
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp [hypGram_apply]

theorem det_sMat : (sMat : Matrix _ _ K).det = 1 := by
  rw [det_hyp3]
  simp

@[expose] noncomputable def sSU (h : UnitaryFieldData p f K) : hypSU h 1 1 :=
  mkHypSU h sMat (sMat_gram h) det_sMat

theorem coe_sSU (h : UnitaryFieldData p f K) :
    (((sSU h : hypSU h 1 1) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      sMat := rfl

theorem sMat_mul_dg (a b d : K) : (sMat : Matrix _ _ K) * dg a b d = dg d b a * sMat := by
  refine mat_ext fun i j hi hj => ?_
  rw [mul_apply, mul_apply, sum_hyp, sum_hyp]
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp

theorem sSU_mul_tau (h : UnitaryFieldData p f K) (x : Kˣ) :
    sSU h * tau h x = tau h (Units.map h.bar.toMonoidHom x)⁻¹ * sSU h := by
  refine Subtype.ext (Units.ext ?_)
  change sMat * tauMat h x = tauMat h (Units.map h.bar.toMonoidHom x)⁻¹ * sMat
  rw [tauMat, tauMat, sMat_mul_dg]
  congr 1
  simp only [Units.val_inv_eq_inv_val, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, map_inv₀, h.bar_bar]
  congr 1 <;> simp [mul_comm]

theorem exists_omega (h : UnitaryFieldData p f K) (hq : p ^ f % 3 = 1) :
    ∃ ω : Kˣ, orderOf ω = 3 ∧ h.bar (ω : K) = ω := by
  have := h.finite
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = p ^ (2 * f) - 1 := by
    rw [Nat.card_units, h.card]
  have h3 : 3 ∣ Nat.card Kˣ := by
    have h1 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (by
      intro h0
      rw [h0, Nat.zero_mod] at hq
      exact absurd hq (by norm_num)))
    have h2 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
    rw [hcard, pow_mul']
    omega
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨ω, hω, ?_⟩
  rw [h.bar_apply, ← Units.val_pow_eq_pow_val, ← pow_mod_orderOf, hω, hq, pow_one]

variable (h : UnitaryFieldData p f K) {ω : Kˣ} (hω : orderOf ω = 3) (hωb : h.bar (ω : K) = ω)
include hω

theorem omega_pow_three : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω

theorem omega_sq_add : (ω : K) ^ 2 + ω + 1 = 0 := by
  have h3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, omega_pow_three hω, Units.val_one]
  have h1 : (ω : K) ≠ 1 := by
    intro h1
    have : ω = 1 := Units.ext h1
    rw [this, orderOf_one] at hω
    exact absurd hω (by norm_num)
  have : ((ω : K) - 1) * ((ω : K) ^ 2 + ω + 1) = 0 := by linear_combination h3
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) h1
  · exact h0

theorem omega_inv : (ω : K)⁻¹ = (ω : K) ^ 2 := by
  have h3 : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, omega_pow_three hω, Units.val_one]
  exact inv_eq_of_mul_eq_one_right (by linear_combination h3)

include hωb

theorem coe_tau_omega :
    (((tau h ω : hypSU h 1 1) : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) =
      dg (ω : K) 1 ((ω : K) ^ 2) := by
  rw [coe_tau, tauMat, hωb, mul_inv_cancel₀ ω.ne_zero, omega_inv hω]

theorem orderOf_tau_omega : orderOf (tau h ω) = 3 := by
  rw [orderOf_injective (tau h) (tau_injective h), hω]

theorem sSU_mul_tau_omega : sSU h * tau h ω = (tau h ω)⁻¹ * sSU h := by
  have hm : Units.map h.bar.toMonoidHom ω = ω := Units.ext hωb
  rw [sSU_mul_tau, hm, map_inv]

theorem tau_omega_mulVec (v : HypIndex 1 1 → K) :
    (tau h ω) • v = fun a => Sum.elim (fun _ => (ω : K) * v a)
      (Sum.elim (fun _ => v a) (fun _ => (ω : K) ^ 2 * v a)) a := by
  change ((tau h ω : hypSU h 1 1) : GL (HypIndex 1 1) K).val *ᵥ v = _
  rw [coe_tau_omega h hω hωb]
  funext a
  rcases idx_cases a with rfl | rfl | rfl <;> simp [dg, Matrix.mulVec_diagonal]

theorem three_smul_single_ie (v : HypIndex 1 1 → K) :
    (3 : K) • Pi.single ie (v ie) = v + (ω : K) ^ 2 • ((tau h ω) • v) +
      (ω : K) • ((tau h ω) • ((tau h ω) • v)) := by
  have hs := omega_sq_add (K := K) hω
  have h3 : (ω : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, omega_pow_three hω, Units.val_one]
  rw [tau_omega_mulVec h hω hωb, tau_omega_mulVec h hω hωb]
  refine vec_ext ?_ ?_ ?_ <;> simp
  · linear_combination (-2 * v ie) * h3
  · linear_combination (-v iw) * hs
  · linear_combination (-v jf) * hs + (-v jf * ((ω : K) + (ω : K) ^ 2)) * h3

end CFSG.RankThree.PartTwo.Sec17.Proof174Host.U3

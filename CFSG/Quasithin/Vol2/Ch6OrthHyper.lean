module

public import CFSG.Quasithin.Vol2.Ch6OrthIrred
public import CFSG.Quasithin.Vol2.Ch5Sec1L34SL2Borel
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin CFSG.Quasithin.JonesParshall Matrix

theorem exists_ker_eq_of_index_two_ch6 {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ x : A, x + x = 0) (χ : A → A →+ ZMod 2)
    (hχ : ∀ a b y, χ (a + b) y = χ a y + χ b y) (hnd : ∀ a, (∀ y, χ a y = 0) → a = 0)
    (H : AddSubgroup A) (hH : ∀ x y, x ∉ H → y ∉ H → x + y ∈ H) :
    ∃ a, ∀ y, y ∈ H ↔ χ a y = 0 := by
  classical
  let _ : Module (ZMod 2) A := AddCommGroup.zmodModule (fun x => by rw [two_nsmul]; exact h2 x)
  have hfin : Module.Finite (ZMod 2) A := Module.Finite.of_finite
  obtain ⟨e⟩ := (Basis.linearEquiv_dual_iff_finiteDimensional (K := ZMod 2)
    (V := A)).mpr inferInstance
  have : Finite (Module.Dual (ZMod 2) A) := Finite.of_equiv _ e.toEquiv
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  let χ' : A → Module.Dual (ZMod 2) A := fun a =>
    { toFun := fun y => χ a y
      map_add' := fun y y' => map_add (χ a) y y'
      map_smul' := fun r y => by
        rw [RingHom.id_apply]
        rcases h01 r with rfl | rfl
        · rw [zero_smul, zero_smul, map_zero]
        · rw [one_smul, one_smul] }
  have hχ' : Function.Injective χ' := by
    intro a a' haa'
    have h1 : ∀ y, χ (a + a') y = 0 := by
      intro y
      have := LinearMap.congr_fun haa' y
      change χ a y = χ a' y at this
      rw [hχ, this]
      exact CharTwo.add_self_eq_zero _
    have h3 := hnd _ h1
    have h4 : a' = -a := eq_neg_of_add_eq_zero_right h3
    rw [h4, neg_eq_of_add_eq_zero_right (h2 a)]
  have hbij : Function.Bijective χ' :=
    hχ'.bijective_of_nat_card_le (Nat.card_congr e.toEquiv).ge
  let ψ : Module.Dual (ZMod 2) A :=
    { toFun := fun w => if w ∈ H then 0 else 1
      map_add' := fun w w' => by
        by_cases hw : w ∈ H <;> by_cases hw' : w' ∈ H
        · have h1 : w + w' ∈ H := H.add_mem hw hw'
          simp only [h1, hw, hw', ↓reduceIte, add_zero]
        · have h1 : w + w' ∉ H := fun h => hw' (by
            have := H.sub_mem h hw
            rwa [add_sub_cancel_left] at this)
          simp only [h1, hw, hw', ↓reduceIte, zero_add]
        · have h1 : w + w' ∉ H := fun h => hw (by
            have := H.sub_mem h hw'
            rwa [add_sub_cancel_right] at this)
          simp only [h1, hw, hw', ↓reduceIte, add_zero]
        · have h1 : w + w' ∈ H := hH w w' hw hw'
          simp only [h1, hw, hw', ↓reduceIte]
          decide
      map_smul' := fun r w => by
        rw [RingHom.id_apply]
        rcases h01 r with rfl | rfl
        · simp
        · simp }
  obtain ⟨a, ha⟩ := hbij.2 ψ
  refine ⟨a, fun w => ?_⟩
  have := LinearMap.congr_fun ha w
  change χ a w = ψ w at this
  rw [this]
  show w ∈ H ↔ (if w ∈ H then (0 : ZMod 2) else 1) = 0
  by_cases hw : w ∈ H
  · simp [hw]
  · simp only [hw, ↓reduceIte, false_iff]
    decide

section Herm

variable {F : Type} [Field F] [CharP F 2] {a : ℕ}

@[expose] def detPolarCh6 (X Y : Matrix (Fin 2) (Fin 2) F) : F :=
  X 0 0 * Y 1 1 + X 1 1 * Y 0 0 + X 0 1 * Y 1 0 + X 1 0 * Y 0 1

omit [CharP F 2] in
theorem detPolarCh6_add_left (X X' Y : Matrix (Fin 2) (Fin 2) F) :
    detPolarCh6 (X + X') Y = detPolarCh6 X Y + detPolarCh6 X' Y := by
  simp only [detPolarCh6, Matrix.add_apply]
  ring

omit [CharP F 2] in
theorem detPolarCh6_add_right (X Y Y' : Matrix (Fin 2) (Fin 2) F) :
    detPolarCh6 X (Y + Y') = detPolarCh6 X Y + detPolarCh6 X Y' := by
  simp only [detPolarCh6, Matrix.add_apply]
  ring

theorem detPolarCh6_eq (X Y : Matrix (Fin 2) (Fin 2) F) :
    detPolarCh6 X Y = (X + Y).det + X.det + Y.det := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  simp only [detPolarCh6, Matrix.det_fin_two, Matrix.add_apply]
  linear_combination (-(X 0 0 * X 1 1) - Y 0 0 * Y 1 1 + X 0 1 * X 1 0 + Y 0 1 * Y 1 0 +
    X 0 1 * Y 1 0 + X 1 0 * Y 0 1) * h2

theorem det_frobPow_ch6 (g : SL2 F) :
    (frobPow a (g : Matrix (Fin 2) (Fin 2) F)).det = 1 := by
  have h := RingHom.map_det (sig a) (g : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.det_coe, map_one] at h
  rw [frobPow_eq_map]
  exact h.symm

theorem det_twistActCh6 (g : SL2 F) (X : Matrix (Fin 2) (Fin 2) F) :
    (twistActCh6 a g X).det = X.det := by
  rw [twistActCh6, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_frobPow_ch6,
    Matrix.SpecialLinearGroup.det_coe]
  ring

omit [CharP F 2] in
theorem twistActCh6_add (g : SL2 F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    twistActCh6 a g (X + Y) = twistActCh6 a g X + twistActCh6 a g Y := by
  rw [twistActCh6, twistActCh6, twistActCh6, Matrix.mul_add, Matrix.add_mul]

theorem detPolarCh6_twist (g : SL2 F) (X Y : Matrix (Fin 2) (Fin 2) F) :
    detPolarCh6 (twistActCh6 a g X) (twistActCh6 a g Y) = detPolarCh6 X Y := by
  rw [detPolarCh6_eq, detPolarCh6_eq, ← twistActCh6_add, det_twistActCh6, det_twistActCh6,
    det_twistActCh6]

theorem exists_herm_pairing_ch6 [Fintype F] (hF : Fintype.card F = 2 ^ (2 * a)) (ha : 0 < a) :
    ∃ (τ : F →+ ZMod 2) (c : F),
      ∀ X ∈ hermA a F, (∀ Y ∈ hermA a F, τ (c * detPolarCh6 X Y) = 0) → X = 0 := by
  classical
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  let τ0 : F →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) F
  obtain ⟨c, hc⟩ : ∃ c : F, τ0 c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact Algebra.trace_ne_zero (ZMod 2) F (LinearMap.ext hcon)
  have hσ : ∀ x : F, sig a (sig a x) = x := sig_sig hF
  obtain ⟨c₀, hc₀⟩ := exists_sig_ne hF ha
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hd : sig a c₀ + c₀ ≠ 0 := by
    intro h0
    apply hc₀
    linear_combination h0 - c₀ * h2
  set s := c₀ / (sig a c₀ + c₀) with hs
  have hss : s + sig a s = 1 := by
    have hσd : sig a (sig a c₀ + c₀) = sig a c₀ + c₀ := by rw [map_add, hσ, add_comm]
    rw [hs, map_div₀, hσd]
    field_simp
    ring
  refine ⟨τ0.toAddMonoidHom, c, fun X hX hX0 => ?_⟩
  have hXc : ∀ Y ∈ hermA a F, detPolarCh6 X Y = 1 → False := fun Y hY h1 => by
    have := hX0 Y hY
    rw [h1, mul_one] at this
    exact hc this
  have h11 : X 1 1 = 0 := by
    by_contra h0
    refine hXc !![(X 1 1)⁻¹, 0; 0, 0] (mem_hermA_of fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp [map_inv₀, hermA_apply hX 1 1]
    · simp [detPolarCh6, h0]
  have h00 : X 0 0 = 0 := by
    by_contra h0
    refine hXc !![0, 0; 0, (X 0 0)⁻¹] (mem_hermA_of fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp [map_inv₀, hermA_apply hX 0 0]
    · simp [detPolarCh6, h0]
  have h10 : X 1 0 = sig a (X 0 1) := (hermA_apply hX 1 0).symm
  have h01 : X 0 1 = 0 := by
    by_contra h0
    set η := sig a (s / X 0 1) with hη
    have hση : sig a η = s / X 0 1 := by rw [hη, hσ]
    refine hXc !![0, η; sig a η, 0] (mem_hermA_of fun i j => ?_) ?_
    · fin_cases i <;> fin_cases j <;> simp [hσ]
    · simp only [detPolarCh6, h00, h11, h10, of_apply, cons_val', cons_val_zero, cons_val_one,
        empty_val', cons_val_fin_one, Fin.isValue, zero_mul, zero_add]
      rw [hση, hη, map_div₀]
      have hσ0 : sig a (X 0 1) ≠ 0 := by
        intro h1
        apply h0
        rw [← hσ (X 0 1), h1, map_zero]
      field_simp
      linear_combination hss
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · change X 1 0 = 0
    rw [h10, h01, map_zero]
  · exact h11

omit [CharP F 2] in
theorem frobPow_swapr_ch6 (r : F) (ha : 0 < 2 ^ a) :
    frobPow a !![(0 : F), 1; 1, r] = !![0, 1; 1, r ^ 2 ^ a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [frobPow, zero_pow ha.ne']

theorem exists_twist_11_eq_zero_ch6 [Finite F] (hF : Nat.card F = 2 ^ (2 * a))
    {v : Matrix (Fin 2) (Fin 2) F} (hv : v ∈ hermA a F) :
    ∃ g : SL2 F, twistActCh6 a g v 1 1 = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ (2 * a) := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hσ : ∀ x : F, sig a (sig a x) = x := sig_sig hF'
  have hpa : 0 < 2 ^ a := by positivity
  by_cases hδ : v 1 1 = 0
  · refine ⟨1, ?_⟩
    have h1 : frobPow a (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [frobPow, zero_pow hpa.ne']
    rw [twistActCh6, Matrix.SpecialLinearGroup.coe_one, h1, Matrix.transpose_one, Matrix.one_mul,
      Matrix.mul_one]
    exact hδ
  have hδq : sig a (v 1 1) = v 1 1 := hermA_apply hv 1 1
  have hαq : sig a (v 0 0) = v 0 0 := hermA_apply hv 0 0
  have h10 : v 1 0 = sig a (v 0 1) := (hermA_apply hv 1 0).symm
  set δ := v 1 1 with hδdef
  set D := v 0 0 * δ + v 0 1 * sig a (v 0 1) with hD
  have hDq : sig a D = D := by
    rw [hD, map_add, map_mul, map_mul, hσ, hαq, hδq]
    ring
  obtain ⟨z, hz⟩ : ∃ z : F, z * sig a z = D / δ ^ 2 := by
    by_cases hD0 : D = 0
    · exact ⟨0, by rw [hD0]; simp⟩
    · have hk0 : D / δ ^ 2 ≠ 0 := div_ne_zero hD0 (pow_ne_zero 2 hδ)
      have hkq : (D / δ ^ 2) ^ 2 ^ a = D / δ ^ 2 := by
        rw [← sig_apply, map_div₀, map_pow, hDq, hδq]
      obtain ⟨z, -, hz⟩ := exists_pow_add_one_eq hF hk0 hkq
      refine ⟨z, ?_⟩
      rw [sig_apply, ← pow_succ']
      exact hz
  set r := z + v 0 1 / δ with hr
  let g : SL2 F := ⟨!![0, 1; 1, r], by
    rw [Matrix.det_fin_two_of]
    linear_combination -h2⟩
  refine ⟨g, ?_⟩
  have hg : (g : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, r] := rfl
  rw [twistActCh6, hg, frobPow_swapr_ch6 r hpa, triple_apply]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    Fin.isValue, one_mul]
  rw [h10, ← sig_apply, hr, map_add, map_div₀, hδq]
  field_simp
  have hz' : z * sig a z * δ ^ 2 = D := by rw [hz]; field_simp
  rw [hD] at hz'
  linear_combination (2 * δ * v 0 1 * sig a (v 0 1) + δ ^ 2 * v 0 0 + δ ^ 2 * v 0 1 * sig a z +
    δ ^ 2 * sig a (v 0 1) * z) * h2 + δ * hz'

theorem exists_unip_fix_ch6 [Fintype F] (hF : Fintype.card F = 2 ^ (2 * a))
    {v : Matrix (Fin 2) (Fin 2) F} (hv : v ∈ hermA a F) (hv11 : v 1 1 = 0) :
    ∃ t₀ : F, t₀ ≠ 0 ∧ twistActCh6 a (uMat t₀) v = v ∧
      ∀ Y ∈ hermA a F, twistActCh6 a (uMat t₀) Y = Y → detPolarCh6 v Y = 0 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hσ : ∀ x : F, sig a (sig a x) = x := sig_sig hF
  have h10 : v 1 0 = sig a (v 0 1) := (hermA_apply hv 1 0).symm
  have key : ∀ t : F, ∀ X ∈ hermA a F, twistActCh6 a (uMat t) X = X →
      t * X 1 1 = 0 ∧ sig a t * X 0 1 + t * sig a (X 0 1) + t * sig a t * X 1 1 = 0 := by
    intro t X hX hfix
    have h := hAct_uMat_sub t hX
    rw [hfix, sub_self] at h
    have e1 := congrFun (congrFun h 0) 1
    have e0 := congrFun (congrFun h 0) 0
    simp only [Matrix.zero_apply, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
      cons_val_fin_one, Fin.isValue] at e0 e1
    exact ⟨e1.symm, e0.symm⟩
  have hfixv : ∀ t : F, sig a t * v 0 1 + t * sig a (v 0 1) = 0 →
      twistActCh6 a (uMat t) v = v := by
    intro t ht
    have h := hAct_uMat_sub t hv
    rw [hv11] at h
    rw [← sub_eq_zero, h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht]
  by_cases hβ : v 0 1 = 0
  · refine ⟨1, one_ne_zero, hfixv 1 (by rw [hβ]; simp), fun Y hY hfix => ?_⟩
    obtain ⟨e1, -⟩ := key 1 Y hY hfix
    rw [one_mul] at e1
    simp only [detPolarCh6, e1, hv11, h10, hβ, map_zero]
    ring
  · have hσβ : sig a (v 0 1) ≠ 0 := by
      intro h0
      apply hβ
      rw [← hσ (v 0 1), h0, map_zero]
    set t₀ := (sig a (v 0 1))⁻¹ with ht₀
    have hσt : sig a t₀ = (v 0 1)⁻¹ := by rw [ht₀, map_inv₀, hσ]
    have ht₀0 : t₀ ≠ 0 := inv_ne_zero hσβ
    refine ⟨t₀, ht₀0, hfixv t₀ ?_, fun Y hY hfix => ?_⟩
    · rw [hσt, ht₀]
      field_simp
      linear_combination h2
    · obtain ⟨e1, e0⟩ := key t₀ Y hY hfix
      have hY11 : Y 1 1 = 0 := (mul_eq_zero.mp e1).resolve_left ht₀0
      have hY10 : Y 1 0 = sig a (Y 0 1) := (hermA_apply hY 1 0).symm
      rw [hY11, mul_zero, add_zero, hσt, ht₀] at e0
      simp only [detPolarCh6, hY11, hv11, hY10, h10, mul_zero, zero_mul, zero_add]
      field_simp at e0
      linear_combination e0

theorem exists_herm_hyperplane_ch6 [Fintype F] {τ : F →+ ZMod 2} {c : F}
    (hnd : ∀ X ∈ hermA a F, (∀ Y ∈ hermA a F, τ (c * detPolarCh6 X Y) = 0) → X = 0)
    (H : AddSubgroup ↥(hermA a F)) (hH : ∀ x y, x ∉ H → y ∉ H → x + y ∈ H) :
    ∃ v : ↥(hermA a F), ∀ Y : ↥(hermA a F),
      Y ∈ H ↔ τ (c * detPolarCh6 (v : Matrix (Fin 2) (Fin 2) F) Y) = 0 := by
  let χ : ↥(hermA a F) → ↥(hermA a F) →+ ZMod 2 := fun v =>
    { toFun := fun Y => τ (c * detPolarCh6 (v : Matrix (Fin 2) (Fin 2) F) Y)
      map_zero' := by
        have : detPolarCh6 (v : Matrix (Fin 2) (Fin 2) F) 0 = 0 := by simp [detPolarCh6]
        simp [this]
      map_add' := fun Y Y' => by
        simp only [AddSubgroup.coe_add, detPolarCh6_add_right, mul_add, map_add] }
  have hχ : ∀ v w Y, χ (v + w) Y = χ v Y + χ w Y := fun v w Y => by
    simp only [χ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddSubgroup.coe_add,
      detPolarCh6_add_left, mul_add, map_add]
  have hnd' : ∀ v, (∀ Y, χ v Y = 0) → v = 0 := fun v hv =>
    Subtype.ext (hnd v v.2 fun Y hY => hv ⟨Y, hY⟩)
  exact exists_ker_eq_of_index_two_ch6 (fun X => hermA_add_self X) χ hχ hnd' H hH

end Herm

end CFSG.Quasithin.H13

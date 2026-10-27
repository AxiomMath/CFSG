module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119Sub
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67L3Glue
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)

section Perm

variable {F : Type*} [Field F]

theorem exists_perm_ne_zero {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) :
    ∃ π : Equiv.Perm (Fin 3), ∀ j, A (π j) j ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_forall, ne_eq, not_not] at hcon
  apply hA
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨j, hj⟩ := hcon σ
  have hz : ∏ i, A (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
  rw [hz, smul_zero]

theorem diag_of_intertwine₂ {τ τ' : F} (hτ1 : τ ≠ 1) (hτ'1 : τ' ≠ 1)
    {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) {l₂ l₃ : F}
    (h₂ : A * diagonal ![1, 1, τ'] = l₂ • (diagonal ![1, 1, τ] * A))
    (h₃ : A * diagonal ![1, τ', 1] = l₃ • (diagonal ![1, τ, 1] * A)) :
    τ' = τ ∧ ∀ i j, i ≠ j → A i j = 0 := by
  obtain ⟨π, hπ⟩ := exists_perm_ne_zero hA
  have e20 : (1 : F) = l₂ * ![1, 1, τ] (π 0) := entry_of_intertwine h₂ (hπ 0)
  have e21 : (1 : F) = l₂ * ![1, 1, τ] (π 1) := entry_of_intertwine h₂ (hπ 1)
  have e22 : τ' = l₂ * ![1, 1, τ] (π 2) := entry_of_intertwine h₂ (hπ 2)
  have e32 : (1 : F) = l₃ * ![1, τ, 1] (π 2) := entry_of_intertwine h₃ (hπ 2)
  have h01 : π 0 ≠ π 1 := fun h => absurd (π.injective h) (by decide)
  have h02 : π 0 ≠ π 2 := fun h => absurd (π.injective h) (by decide)
  have h12 : π 1 ≠ π 2 := fun h => absurd (π.injective h) (by decide)
  have v2 : ∀ k : Fin 3, k ≠ 2 → ![1, 1, τ] k = (1 : F) := by
    intro k hk
    fin_cases k
    · rfl
    · rfl
    · exact (hk rfl).elim
  have hπ0 : π 0 ≠ 2 := by
    intro h
    have hπ1 : π 1 ≠ 2 := fun h' => h01 (h.trans h'.symm)
    rw [v2 _ hπ1] at e21
    have h2 : ![1, 1, τ] (π 0) = τ := by rw [h]; rfl
    rw [h2] at e20
    exact hτ1 (by linear_combination -e20 + τ * e21)
  have hπ1 : π 1 ≠ 2 := by
    intro h
    have hπ0' : π 0 ≠ 2 := fun h' => h01 (h'.trans h.symm)
    rw [v2 _ hπ0'] at e20
    have h2 : ![1, 1, τ] (π 1) = τ := by rw [h]; rfl
    rw [h2] at e21
    exact hτ1 (by linear_combination τ * e20 - e21)
  have hperm : ∀ a b c : Fin 3, a ≠ b → a ≠ c → b ≠ c → a ≠ 2 → b ≠ 2 → c = 2 := by
    intro a b c
    fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
  have hπ2 : π 2 = 2 := hperm (π 0) (π 1) (π 2) h01 h02 h12 hπ0 hπ1
  have hl₂ : l₂ = 1 := by
    rw [v2 _ hπ0] at e20
    linear_combination -e20
  have h2τ : ![1, 1, τ] (π 2) = τ := by rw [hπ2]; rfl
  have hτ : τ' = τ := by
    rw [h2τ, hl₂] at e22
    linear_combination e22
  have h2τ' : ![1, τ, 1] (π 2) = (1 : F) := by rw [hπ2]; rfl
  have hl₃ : l₃ = 1 := by
    rw [h2τ'] at e32
    linear_combination -e32
  refine ⟨hτ, fun i j hij => ?_⟩
  by_contra hA0
  have f2 := entry_of_intertwine h₂ hA0
  have f3 := entry_of_intertwine h₃ hA0
  rw [hl₂, hτ] at f2
  rw [hl₃, hτ] at f3
  fin_cases i <;> fin_cases j <;> simp at hij f2 f3 <;>
    first | exact hτ1 f2 | exact hτ1 f2.symm | exact hτ1 f3 | exact hτ1 f3.symm

end Perm

section FieldFix

variable {F : Type*} [Field F]

theorem pow_apply_of_eq_pow {σ : F ≃+* F} {ζ : F} {i : ℕ} (h : σ ζ = ζ ^ i) (k : ℕ) :
    (σ ^ k) ζ = ζ ^ (i ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, RingAut.mul_apply, h, map_pow, ih, ← pow_mul, pow_succ]

theorem fieldAut_fix_of_pow_fix {p : ℕ} (hp : p.Prime) {σ : F ≃+* F} {ζ : F}
    (hζ : IsPrimitiveRoot ζ p) (hσ : (σ ^ p) ζ = ζ) : ∀ a : F, a ^ p = 1 → σ a = a := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hσζ : (σ ζ) ^ p = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
  obtain ⟨i, hi, hσi⟩ := hζ.eq_pow_of_pow_eq_one hσζ
  have hk := pow_apply_of_eq_pow hσi.symm p
  rw [hσ] at hk
  have hi1 : i = 1 := by
    have h1 : ζ ^ (i ^ p) = ζ ^ 1 := by rw [pow_one]; exact hk.symm
    have hord : orderOf ζ = p := hζ.eq_orderOf.symm
    have h2 : ζ ^ (i ^ p % p) = ζ ^ (1 % p) := by
      have e1 := pow_mod_orderOf ζ (i ^ p)
      have e2 := pow_mod_orderOf ζ 1
      rw [hord] at e1 e2
      rw [e1, e2]
      exact h1
    have h3 : i ^ p % p = 1 % p :=
      hζ.pow_inj (Nat.mod_lt _ hp.pos) (Nat.mod_lt _ hp.pos) h2
    have h4 : (i : ZMod p) ^ p = (i : ZMod p) := by
      haveI := Fact.mk hp
      exact ZMod.pow_card _
    have h5 : i ^ p % p = i % p := by
      refine (ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_
      push_cast
      exact h4
    rw [Nat.mod_eq_of_lt hi, h3, Nat.mod_eq_of_lt hp.one_lt] at h5
    exact h5.symm
  subst hi1
  rw [pow_one] at hσi
  intro a ha
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one ha
  rw [map_pow, ← hσi]

end FieldFix

section Odd

variable {F : Type} [Field F]

theorem exists_scalar_of_commute [Finite F] {B y : GL (Fin 3) F} {σ : F ≃+* F}
    (h : conjAut 3 F B * fieldAut 3 F σ * conjAut 3 F y =
      conjAut 3 F y * (conjAut 3 F B * fieldAut 3 F σ)) :
    ∃ c : Fˣ, B * GeneralLinearGroup.map (σ : F →+* F) y =
      y * B * GeneralLinearGroup.scalar (Fin 3) c := by
  obtain ⟨-, -, hfc, -, -, -, -⟩ := standard_automorphism_transport (n := 3) (K := F)
  have hfc' : fieldAut 3 F σ * conjAut 3 F y =
      conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) y) * fieldAut 3 F σ :=
    mul_inv_eq_iff_eq_mul.mp (hfc σ y)
  have h1 : conjAut 3 F (B * GeneralLinearGroup.map (σ : F →+* F) y) * fieldAut 3 F σ =
      conjAut 3 F (y * B) * fieldAut 3 F σ := by
    rw [map_mul, map_mul]
    calc conjAut 3 F B * conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) y) * fieldAut 3 F σ
        = conjAut 3 F B * (conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) y) *
            fieldAut 3 F σ) := by rw [mul_assoc]
      _ = conjAut 3 F B * (fieldAut 3 F σ * conjAut 3 F y) := by rw [hfc']
      _ = conjAut 3 F B * fieldAut 3 F σ * conjAut 3 F y := by rw [mul_assoc]
      _ = conjAut 3 F y * (conjAut 3 F B * fieldAut 3 F σ) := h
      _ = conjAut 3 F y * conjAut 3 F B * fieldAut 3 F σ := by rw [mul_assoc]
  have h2 : conjAut 3 F (B * GeneralLinearGroup.map (σ : F →+* F) y) =
      conjAut 3 F (y * B) := mul_right_cancel h1
  have h3 : conjAut 3 F ((y * B)⁻¹ * (B * GeneralLinearGroup.map (σ : F →+* F) y)) *
      fieldAut 3 F (1 : F ≃+* F) = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, h2, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ h3
  refine ⟨c, ?_⟩
  rw [hc]
  group


theorem matrix_of_gl_eq {B y y' : GL (Fin 3) F} {c : Fˣ}
    (h : B * y' = y * B * GeneralLinearGroup.scalar (Fin 3) c) :
    (B : Matrix (Fin 3) (Fin 3) F) * (y' : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • ((y : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F)) := by
  have h1 := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
  rw [h1, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]


theorem coe_map_diagUnits_one_one (σ : F ≃+* F) (τ : Fˣ) :
    ((GeneralLinearGroup.map (σ : F →+* F) (diagUnits 1 1 τ) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = diagonal ![1, 1, σ (τ : F)] := by
  rw [map_diagUnits, coe_diagUnits]
  simp

theorem coe_map_diagUnits_one_mid (σ : F ≃+* F) (τ : Fˣ) :
    ((GeneralLinearGroup.map (σ : F →+* F) (diagUnits 1 τ 1) : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = diagonal ![1, σ (τ : F), 1] := by
  rw [map_diagUnits, coe_diagUnits]
  simp

theorem odd_aut_diag [Finite F] {m : ℕ} (hm : Odd m) {τ : Fˣ} (hτ1 : τ ≠ 1)
    {β : MulAut (projectiveSL 3 F)} (hβm : β ^ m = 1)
    (hc₂ : β * conjAut 3 F (diagUnits 1 1 τ) = conjAut 3 F (diagUnits 1 1 τ) * β)
    (hc₃ : β * conjAut 3 F (diagUnits 1 τ 1) = conjAut 3 F (diagUnits 1 τ 1) * β) :
    ∃ (B : GL (Fin 3) F) (σ : F ≃+* F), β = conjAut 3 F B * fieldAut 3 F σ ∧
      ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have hβE : β ∈ semilinearAutGroup 3 F :=
    CFSG.GH74.GLS.Stage2.Bender.Thm1.mem_semilinearAutGroup_of_pow_eq_one (le_refl 3) hm hβm
  obtain ⟨B, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp hβE
  obtain ⟨c₂, h₂⟩ := exists_scalar_of_commute hc₂
  obtain ⟨c₃, h₃⟩ := exists_scalar_of_commute hc₃
  have e₂ := matrix_of_gl_eq h₂
  have e₃ := matrix_of_gl_eq h₃
  rw [coe_map_diagUnits_one_one, coe_diagUnits] at e₂
  rw [coe_map_diagUnits_one_mid, coe_diagUnits] at e₃
  simp only [Units.val_one] at e₂ e₃
  have hτ1' : (τ : F) ≠ 1 := fun h => hτ1 (Units.ext h)
  have hσ1 : σ (τ : F) ≠ 1 := fun h => hτ1' (σ.injective (by rw [h, map_one]))
  have hdet : (B : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := det_ne_zero_gl B
  exact ⟨B, σ, rfl, (diag_of_intertwine₂ hτ1' hσ1 hdet e₂ e₃).2⟩


theorem eq_of_proj_diagSL_eq {a b c a' b' c' : F} {h : a * b * c = 1} {h' : a' * b' * c' = 1}
    (he : proj 3 F (diagSL a b c h) = proj 3 F (diagSL a' b' c' h')) (hc : c = c') :
    a = a' ∧ b = b' := by
  obtain ⟨u, -, hum⟩ := mem_scalars.mp (proj_eq_proj_iff.mp he)
  have h1 : ((diagSL a' b' c' h' : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (diagSL a b c h : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (u : F) := by
    rw [← hum, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
  have e0 := congrFun (congrFun h1 0) 0
  have e1 := congrFun (congrFun h1 1) 1
  have e2 := congrFun (congrFun h1 2) 2
  simp [diagSL, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply,
    diagonal_apply] at e0 e1 e2
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at h
  have hu : (u : F) = 1 := by
    have : c * (u : F) = c * 1 := by rw [mul_one, ← e2, hc]
    exact mul_left_cancel₀ hc0 this
  rw [hu] at e0 e1
  exact ⟨by simpa using e0.symm, by simpa using e1.symm⟩

theorem conjAut_fix_proj_diagSL {B : GL (Fin 3) F}
    (hB : ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0) (a b c : F)
    (h : a * b * c = 1) :
    conjAut 3 F B (proj 3 F (diagSL a b c h)) = proj 3 F (diagSL a b c h) := by
  rw [conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  exact conj_diag_eq hB _ ![a, b, c] rfl

theorem pow_apply_proj_diagSL {B : GL (Fin 3) F}
    (hB : ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0) (σ : F ≃+* F) (a b c : F)
    (h : a * b * c = 1) (k : ℕ) :
    ∃ h' : (σ ^ k) a * (σ ^ k) b * (σ ^ k) c = 1,
      ((conjAut 3 F B * fieldAut 3 F σ) ^ k) (proj 3 F (diagSL a b c h)) =
        proj 3 F (diagSL ((σ ^ k) a) ((σ ^ k) b) ((σ ^ k) c) h') := by
  induction k with
  | zero => exact ⟨by simpa using h, by simp⟩
  | succ k ih =>
    obtain ⟨h', hk⟩ := ih
    have h'' : (σ ^ (k + 1)) a * (σ ^ (k + 1)) b * (σ ^ (k + 1)) c = 1 := by
      rw [pow_succ', RingAut.mul_apply, RingAut.mul_apply, RingAut.mul_apply, ← map_mul,
        ← map_mul, h', map_one]
    refine ⟨h'', ?_⟩
    have hs : σ ((σ ^ k) a) * σ ((σ ^ k) b) * σ ((σ ^ k) c) = 1 := by
      rw [← map_mul, ← map_mul, h', map_one]
    have e : ∀ x, (σ ^ (k + 1)) x = σ ((σ ^ k) x) := fun x => by
      rw [pow_succ', RingAut.mul_apply]
    rw [pow_succ', MulAut.mul_apply, hk, MulAut.mul_apply, fieldAut_proj_diagSL σ _ _ _ h' hs,
      conjAut_fix_proj_diagSL hB]
    congr 1
    apply Subtype.ext
    simp only [coe_diagSL, e]


theorem exists_isPrimitiveRoot [Finite F] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1) :
    ∃ ζ : F, IsPrimitiveRoot ζ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨(x : F), IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)⟩

theorem aut_fixes_torus [Finite F] {p : ℕ} (hp : p.Prime) (hpF : p ∣ Nat.card F - 1)
    {B : GL (Fin 3) F} (hB : ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0)
    {σ : F ≃+* F} (hβ : (conjAut 3 F B * fieldAut 3 F σ) ^ p = 1) {z : projectiveSL 3 F}
    (hz : z ∈ torSub p F) : (conjAut 3 F B * fieldAut 3 F σ) z = z := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot hp hpF
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have h0 : ζ * ζ⁻¹ * 1 = 1 := by field_simp
  obtain ⟨h', hk⟩ := pow_apply_proj_diagSL hB σ ζ ζ⁻¹ 1 h0 p
  rw [hβ, MulAut.one_apply] at hk
  have hσζ : (σ ^ p) ζ = ζ := (eq_of_proj_diagSL_eq hk (by simp)).1.symm
  have hfix := fieldAut_fix_of_pow_fix hp hζ hσζ
  obtain ⟨a, b, c, h, ha, hb, hc, rfl⟩ := (mem_torSub_iff hp).mp hz
  have hs : σ a * σ b * σ c = 1 := by rw [← map_mul, ← map_mul, h, map_one]
  rw [MulAut.mul_apply, fieldAut_proj_diagSL σ a b c h hs, conjAut_fix_proj_diagSL hB]
  congr 1
  apply Subtype.ext
  simp only [coe_diagSL, hfix a ha, hfix b hb, hfix c hc]

theorem exists_diagUnits_of_isDiag {B : GL (Fin 3) F}
    (hB : ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    ∃ a b c : Fˣ, B = diagUnits a b c := by
  have hd : (B : Matrix (Fin 3) (Fin 3) F) = diagonal ![(B : Matrix (Fin 3) (Fin 3) F) 0 0,
      (B : Matrix (Fin 3) (Fin 3) F) 1 1, (B : Matrix (Fin 3) (Fin 3) F) 2 2] := by
    ext i j
    by_cases hij : i = j
    · subst hij
      fin_cases i <;> simp
    · rw [hB i j hij, diagonal_apply_ne _ hij]
  have hdet := det_ne_zero_gl B
  rw [hd, det_diagonal, Fin.prod_univ_three] at hdet
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at hdet
  have h0 : (B : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 :=
    left_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  have h1 : (B : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 :=
    right_ne_zero_of_mul (left_ne_zero_of_mul hdet)
  have h2 : (B : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := right_ne_zero_of_mul hdet
  refine ⟨Units.mk0 _ h0, Units.mk0 _ h1, Units.mk0 _ h2, Units.ext ?_⟩
  rw [coe_diagUnits]
  simp only [Units.val_mk0]
  exact hd

theorem aut_maps_rootSub {B : GL (Fin 3) F}
    (hB : ∀ i j, i ≠ j → (B : Matrix (Fin 3) (Fin 3) F) i j = 0) (σ : F ≃+* F)
    {u : projectiveSL 3 F} (hu : u ∈ rootSub F) :
    (conjAut 3 F B * fieldAut 3 F σ) u ∈ rootSub F := by
  obtain ⟨a, b, c, rfl⟩ := exists_diagUnits_of_isDiag hB
  rw [MulAut.mul_apply]
  exact conjAut_diagUnits_mem_rootSub a b c (fieldAut_mem_rootSub σ hu)

end Odd

end CFSG.RankThree.PartTwo.Sec21.Hering2119

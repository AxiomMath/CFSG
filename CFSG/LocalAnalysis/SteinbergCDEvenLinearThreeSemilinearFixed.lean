module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.LocalAnalysis.SteinbergCD

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification.CatalogueBHigherLinearField

section Centralizer

variable (n : ℕ) (K : Type*) [Field K]

@[expose] def slCent (X : Matrix (Fin n) (Fin n) K) : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | X * (g : Matrix (Fin n) (Fin n) K) = g * X}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul] at *
    rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * a = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (a : Matrix (Fin n) (Fin n) K) * ((a⁻¹ : SpecialLinearGroup (Fin n) K)) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc X * ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * a * X *
            ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [h1, one_mul]
      _ = ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * (X * a) *
            ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [ha]; simp only [mul_assoc]
      _ = ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * X *
            ((a : Matrix (Fin n) (Fin n) K) *
              ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
          simp only [mul_assoc]
      _ = _ := by rw [h2, mul_one]

variable {n K}

theorem mem_slCent {X : Matrix (Fin n) (Fin n) K} {g : SpecialLinearGroup (Fin n) K} :
    g ∈ slCent n K X ↔ X * (g : Matrix (Fin n) (Fin n) K) = g * X :=
  Iff.rfl

theorem slCent_add_one (X : Matrix (Fin n) (Fin n) K) : slCent n K (X + 1) = slCent n K X := by
  ext g
  rw [mem_slCent, mem_slCent, add_mul, mul_add, one_mul, mul_one]
  exact add_left_inj _

theorem card_slCent_eq_of_mul_eq_mul {X Y : Matrix (Fin n) (Fin n) K} (P : GL (Fin n) K)
    (hP : X * (P : Matrix (Fin n) (Fin n) K) = (P : Matrix (Fin n) (Fin n) K) * Y) :
    Nat.card (slCent n K X) = Nat.card (slCent n K Y) := by
  set p : Matrix (Fin n) (Fin n) K := ↑P
  set p' : Matrix (Fin n) (Fin n) K := ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hpp' : p * p' = 1 := by
    simp only [p, p']
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hp'p : p' * p = 1 := by
    simp only [p, p']
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hY : Y = p' * X * p := by rw [mul_assoc, hP, ← mul_assoc, hp'p, one_mul]
  have hX : X = p * Y * p' := by rw [← hP, mul_assoc, hpp', mul_one]
  set φ := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K P⁻¹
  have hφ : ∀ g, ((φ g : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      p' * g * p := fun g => by
    rw [coe_slConjugation, inv_inv]
  have hmap : (slCent n K X).map φ.toMonoidHom = slCent n K Y := by
    ext h
    constructor
    · rintro ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, mem_slCent] at hg
      rw [mem_slCent, MulEquiv.coe_toMonoidHom, hφ]
      calc Y * (p' * g * p) = p' * X * (p * p') * g * p := by rw [hY]; simp only [mul_assoc]
        _ = p' * (X * g) * p := by rw [hpp', mul_one]; simp only [mul_assoc]
        _ = p' * (g * X) * p := by rw [hg]
        _ = p' * g * (p * p') * X * p := by rw [hpp', mul_one]; simp only [mul_assoc]
        _ = p' * g * p * Y := by rw [hY]; simp only [mul_assoc]
    · intro hh
      rw [mem_slCent] at hh
      refine ⟨φ.symm h, ?_, by simp⟩
      have hψ : ((φ.symm h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          p * h * p' := by
        have h1 := hφ (φ.symm h)
        rw [MulEquiv.apply_symm_apply] at h1
        calc ((φ.symm h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
            = (p * p') * (φ.symm h : SpecialLinearGroup (Fin n) K) * (p * p') := by
              rw [hpp', one_mul, mul_one]
          _ = p * (p' * (φ.symm h : SpecialLinearGroup (Fin n) K) * p) * p' := by
              simp only [mul_assoc]
          _ = p * h * p' := by rw [← h1]
      rw [SetLike.mem_coe, mem_slCent, hψ]
      calc X * (p * h * p') = p * Y * (p' * p) * h * p' := by rw [hX]; simp only [mul_assoc]
        _ = p * (Y * h) * p' := by rw [hp'p, mul_one]; simp only [mul_assoc]
        _ = p * (h * Y) * p' := by rw [hh]
        _ = p * h * (p' * p) * Y * p' := by rw [hp'p, mul_one]; simp only [mul_assoc]
        _ = p * h * p' * X := by rw [hX]; simp only [mul_assoc]
  rw [← hmap, Subgroup.card_map_of_injective φ.injective]

end Centralizer

section NormalForm

variable {K : Type*} [Field K]

abbrev unitE : Matrix (Fin 3) (Fin 3) K := single 0 2 1

theorem exists_mul_eq_mul_unitE {N : Matrix (Fin 3) (Fin 3) K} (hN : N * N = 0) (hN0 : N ≠ 0) :
    ∃ P : GL (Fin 3) K,
      N * (P : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) * unitE := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → K, N *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hN0
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    rw [mulVec_single_one] at this
    simpa using this
  set p₁ := N *ᵥ v with hp₁
  set f := Matrix.toLin' N
  have hf : ∀ w, f w = N *ᵥ w := fun w => Matrix.toLin'_apply N w
  have hrange : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨w, rfl⟩
    rw [LinearMap.mem_ker, hf, hf, mulVec_mulVec, hN, zero_mulVec]
  have hsum := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hsum
  have hle := Submodule.finrank_mono hrange
  have hpos : 0 < Module.finrank K (LinearMap.range f) :=
    Module.finrank_pos_iff_exists_ne_zero.2
      ⟨⟨p₁, ⟨v, hf v⟩⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hker : Module.finrank K (LinearMap.ker f) = 2 := by omega
  have hp₁ker : p₁ ∈ LinearMap.ker f := hrange ⟨v, hf v⟩
  have hspan : K ∙ p₁ < LinearMap.ker f := by
    apply Submodule.lt_of_le_of_finrank_lt_finrank
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 hp₁ker
    · rw [finrank_span_singleton hv, hker]
      norm_num
  obtain ⟨p₂, hp₂, hp₂'⟩ := IsConcreteLE.exists_of_lt hspan
  have hNp₁ : N *ᵥ p₁ = 0 := by rw [← hf]; exact hp₁ker
  have hNp₂ : N *ᵥ p₂ = 0 := by rw [← hf]; exact hp₂
  have hind : LinearIndependent K ![p₁, p₂, v] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_three] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at hg
    have h2 : g 2 = 0 := by
      have := congrArg (N *ᵥ ·) hg
      simp only [mulVec_add, mulVec_smul, hNp₁, hNp₂, smul_zero, zero_add, mulVec_zero] at this
      exact (smul_eq_zero.1 this).resolve_right hv
    rw [h2, zero_smul, add_zero] at hg
    have h1 : g 1 = 0 := by
      by_contra h1
      apply hp₂'
      have e : g 0 • p₁ = -(g 1 • p₂) := eq_neg_of_add_eq_zero_left hg
      refine Submodule.mem_span_singleton.2 ⟨-(g 1)⁻¹ * g 0, ?_⟩
      rw [mul_smul, e, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ h1, one_smul]
    rw [h1, zero_smul, add_zero] at hg
    have h0 : g 0 = 0 := (smul_eq_zero.1 hg).resolve_right hv
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  set M : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![p₁, p₂, v] j i
  have hMcol : M.col = ![p₁, p₂, v] := by
    ext j i
    rfl
  have hunit : IsUnit M := linearIndependent_cols_iff_isUnit.1 (by rw [hMcol]; exact hind)
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  ext i j
  have e1 := congrFun hNp₁ i
  have e2 := congrFun hNp₂ i
  simp only [mulVec, dotProduct, Fin.sum_univ_three, Pi.zero_apply] at e1 e2
  fin_cases j
  · simp [M, Matrix.mul_apply, Fin.sum_univ_three, e1]
  · simp [M, Matrix.mul_apply, Fin.sum_univ_three, e2]
  · simp [M, Matrix.mul_apply, Fin.sum_univ_three, hp₁, mulVec, dotProduct]

@[expose] def centMat (a : Kˣ) (b c e : K) : Matrix (Fin 3) (Fin 3) K :=
  !![(a : K), b, c; 0, ((a⁻¹ : Kˣ) : K) ^ 2, e; 0, 0, (a : K)]

theorem det_centMat (a : Kˣ) (b c e : K) : (centMat a b c e).det = 1 := by
  rw [centMat, det_fin_three]
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two, empty_val',
    cons_val_fin_one, head_cons, head_fin_const, tail_cons, mul_zero, zero_mul, sub_zero,
    add_zero]
  rw [Units.val_inv_eq_inv_val]
  field_simp

theorem unitE_mul_centMat (a : Kˣ) (b c e : K) :
    unitE * centMat a b c e = centMat a b c e * unitE := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centMat, unitE, Matrix.mul_apply, Matrix.single_apply]

theorem slCent_unitE_entries {g : SpecialLinearGroup (Fin 3) K} (hg : g ∈ slCent 3 K unitE) :
    (g : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (g : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 2 2 = (g : Matrix (Fin 3) (Fin 3) K) 0 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) 0 0 * (g : Matrix (Fin 3) (Fin 3) K) 0 0 *
        (g : Matrix (Fin 3) (Fin 3) K) 1 1 = 1 := by
  rw [mem_slCent] at hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h02 := congrFun (congrFun hg 0) 2
  have h12 := congrFun (congrFun hg 1) 2
  simp [unitE, Matrix.mul_apply, Matrix.single_apply] at h00 h01 h02 h12
  have hdet := g.2
  rw [det_fin_three, h00, h01, h02, ← h12] at hdet
  refine ⟨h12.symm, h00, h01, h02, ?_⟩
  linear_combination hdet

theorem card_slCent_unitE [Finite K] :
    Nat.card (slCent 3 K unitE) = (Nat.card K - 1) * Nat.card K ^ 3 := by
  classical
  have hne : ∀ g : slCent 3 K unitE,
      ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro g h
    have := (slCent_unitE_entries g.2).2.2.2.2
    rw [h, zero_mul, zero_mul] at this
    exact zero_ne_one this
  let e : slCent 3 K unitE ≃ Kˣ × K × K × K :=
    { toFun := fun g => (Units.mk0 _ (hne g),
        ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 1,
        ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2,
        ((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2)
      invFun := fun x => ⟨⟨centMat x.1 x.2.1 x.2.2.1 x.2.2.2, det_centMat _ _ _ _⟩,
        unitE_mul_centMat _ _ _ _⟩
      left_inv := fun g => by
        obtain ⟨h10, h20, h21, h22, hdet⟩ := slCent_unitE_entries g.2
        have hg0 := hne g
        apply Subtype.ext
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [centMat, h10, h20, h21, h22]
        exact (eq_inv_of_mul_eq_one_left (by linear_combination hdet)).symm
      right_inv := fun x => by
        obtain ⟨a, b, c, e⟩ := x
        simp only [centMat, of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_two,
          empty_val', cons_val_fin_one, head_cons, tail_cons]
        rw [Units.mk0_val] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_prod, Nat.card_units]
  ring

end NormalForm

section Trace

open CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {K : Type*} [Field K] {n : ℕ}

theorem comm_of_proj_slConjugation_eq {B : GL (Fin n) K} {g : SpecialLinearGroup (Fin n) K}
    (htr : (B : Matrix (Fin n) (Fin n) K).trace ≠ 0)
    (h : proj n K (slConjugation n K B g) = proj n K g) :
    (B : Matrix (Fin n) (Fin n) K) * g = g * B := by
  set S := slConjugation n K B g
  obtain ⟨c, -, hc⟩ := mem_scalars.1 (proj_eq_proj_iff.1 h)
  set b : Matrix (Fin n) (Fin n) K := ↑B
  set b' : Matrix (Fin n) (Fin n) K := ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set G : Matrix (Fin n) (Fin n) K := ↑g
  set G' : Matrix (Fin n) (Fin n) K := ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K)
  have hbb : b' * b = 1 := by
    simp only [b, b']
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hGG : G * G' = 1 := by
    simp only [G, G']
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hG'G : G' * G = 1 := by
    simp only [G, G']
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hS : (S : Matrix (Fin n) (Fin n) K) = b * G * b' := coe_slConjugation B g
  have hG : G = (c : K) • (b * G * b') := by
    have h1 : (S : Matrix (Fin n) (Fin n) K) * ((S⁻¹ * g : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = G := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    rw [hc, hS, scalar_apply, ← smul_one_eq_diagonal, mul_smul_comm, mul_one] at h1
    exact h1.symm
  have hGb : G * b = (c : K) • (b * G) := by
    calc G * b = (c : K) • (b * G * (b' * b)) := by
          nth_rewrite 1 [hG]
          rw [smul_mul_assoc]
          simp only [mul_assoc]
      _ = (c : K) • (b * G) := by rw [hbb, mul_one]
  have hb : b = (c : K) • (G' * b * G) := by
    calc b = G' * (G * b) := by rw [← mul_assoc, hG'G, one_mul]
      _ = (c : K) • (G' * b * G) := by rw [hGb, mul_smul_comm]; simp only [mul_assoc]
  have htr' : b.trace = (c : K) * b.trace := by
    have h1 := congrArg Matrix.trace hb
    rw [trace_smul, smul_eq_mul, trace_mul_comm (G' * b) G, ← mul_assoc, hGG, one_mul] at h1
    exact h1
  have hc1 : (c : K) = 1 := by
    have h1 : ((c : K) - 1) * b.trace = 0 := by linear_combination -htr'
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_right htr)
  rw [hc1, one_smul] at hGb
  exact hGb.symm

end Trace

section Inner

variable {K : Type*} [Field K]

theorem card_fixed_conjAut_dvd [Finite K] [CharP K 2] (A : GL (Fin 3) K)
    (hA : orderOf (conjAut 3 K A) = 2) :
    Nat.card (TauCeti.fixedSubgroup (conjAut 3 K A).toMonoidHom) ∣
      Nat.card K ^ 3 * (Nat.card K - 1) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hA2 : conjAut 3 K (A * A) = 1 := by
    rw [map_mul, ← pow_two, ← hA, pow_orderOf_eq_one]
  have hA1 : conjAut 3 K A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hA
    norm_num at hA
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (A * A) 1
    (by rw [map_one, mul_one]; exact hA2)
  obtain ⟨m, hm⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (c : K)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact c.ne_zero hm
  set u : Kˣ := Units.mk0 m hm0
  have hcu : c = u * u := Units.ext (by rw [Units.val_mul, Units.val_mk0, hm])
  set B := GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A with hB
  have hcB : conjAut 3 K B = conjAut 3 K A := by rw [hB, map_mul, conjAut_scalar, one_mul]
  have hBB : B * B = 1 := by
    rw [hB]
    calc GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A * (GeneralLinearGroup.scalar (Fin 3) u⁻¹ * A)
        = GeneralLinearGroup.scalar (Fin 3) u⁻¹ * GeneralLinearGroup.scalar (Fin 3) u⁻¹ *
            (A * A) := by
          rw [mul_assoc, ← mul_assoc A, ← GeneralLinearGroup.scalar_commute u⁻¹ A]
          simp only [mul_assoc]
      _ = 1 := by
          rw [← hc, ← map_mul, ← map_mul, hcu, ← map_one (GeneralLinearGroup.scalar (Fin 3))]
          congr 1
          group
  have hBinv : B⁻¹ = B := inv_eq_of_mul_eq_one_right hBB
  set M : Matrix (Fin 3) (Fin 3) K := ↑B
  have hMM : M * M = 1 := by
    simp only [M]
    rw [← Units.val_mul, hBB, Units.val_one]
  set N := M + 1
  have hNN : N * N = 0 := by
    simp only [N, add_mul, mul_add, hMM, mul_one, one_mul]
    rw [show (1 : Matrix (Fin 3) (Fin 3) K) + M + (M + 1) = (2 : K) • (M + 1) by
      rw [two_smul]; abel, h2, zero_smul]
  have hN0 : N ≠ 0 := by
    intro h
    apply hA1
    rw [← hcB]
    have hM1 : B = 1 := Units.ext (by
      rw [Units.val_one]
      change M = 1
      have : M = M + 1 + 1 := by
        rw [add_assoc, show (1 : Matrix (Fin 3) (Fin 3) K) + 1 = (2 : K) • 1 by rw [two_smul],
          h2, zero_smul, add_zero]
      rw [this, show M + 1 = N from rfl, h, zero_add])
    rw [hM1, map_one]
  have htrN : N.trace = 0 :=
    (isNilpotent_trace_of_isNilpotent ⟨2, by rw [pow_two, hNN]⟩).eq_zero
  have htrM : M.trace ≠ 0 := by
    have h1 : M.trace = N.trace + 1 := by
      rw [show M = N + 1 by
        simp only [N]
        rw [add_assoc, show (1 : Matrix (Fin 3) (Fin 3) K) + 1 = (2 : K) • 1 by rw [two_smul],
          h2, zero_smul, add_zero], trace_add, trace_one, Fintype.card_fin]
      linear_combination h2
    rw [h1, htrN, zero_add]
    exact one_ne_zero
  have hfix :
      TauCeti.fixedSubgroup (conjAut 3 K A).toMonoidHom = (slCent 3 K M).map (proj 3 K) := by
    ext x
    rw [TauCeti.mem_fixedSubgroup, MulEquiv.coe_toMonoidHom, ← hcB]
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := proj_surjective 3 K x
      rw [conjAut_proj] at hx
      exact ⟨g, comm_of_proj_slConjugation_eq htrM hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      rw [conjAut_proj]
      congr 1
      apply Subtype.ext
      rw [coe_slConjugation, hBinv]
      change M * g * M = g
      rw [mem_slCent.1 hg, mul_assoc, hMM, mul_one]
  obtain ⟨P, hP⟩ := exists_mul_eq_mul_unitE hNN hN0
  have hcard : Nat.card (slCent 3 K M) = (Nat.card K - 1) * Nat.card K ^ 3 := by
    rw [← slCent_add_one, card_slCent_eq_of_mul_eq_mul P hP, card_slCent_unitE]
  rw [hfix, mul_comm, ← hcard]
  exact Subgroup.card_map_dvd _ _

end Inner

section Field

variable (n : ℕ) (K : Type*) [Field K]

@[expose] noncomputable def projToPGL : projectiveSL n K →* ProjGenLinGroup (Fin n) K :=
  QuotientGroup.lift (scalars n K) SpecialLinearGroup.toPGL
    ((scalars_eq_center n K).trans SpecialLinearGroup.toPGL_ker.symm).le

variable {n K}

theorem projToPGL_injective : Function.Injective (projToPGL n K) :=
  (QuotientGroup.injective_lift_iff _ _ _).2
    ((scalars_eq_center n K).trans SpecialLinearGroup.toPGL_ker.symm)

theorem projToPGL_proj (g : SpecialLinearGroup (Fin n) K) :
    projToPGL n K (proj n K g) = ProjGenLinGroup.mk (SpecialLinearGroup.toGL g) :=
  rfl

theorem projToPGL_fieldAut (σ : K ≃+* K) (x : projectiveSL n K) :
    projToPGL n K (fieldAut n K σ x) = pglFieldAut (Fin n) K σ (projToPGL n K x) := by
  obtain ⟨g, rfl⟩ := proj_surjective n K x
  rw [fieldAut_proj, projToPGL_proj, projToPGL_proj]
  change _ = ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom (SpecialLinearGroup.toGL g))
  congr 1
  ext i j
  rfl

theorem card_projGenLinGroup_three (F : Type*) [Field F] [Finite F] :
    Nat.card (ProjGenLinGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  have hGL := Matrix.card_GL_field (𝔽 := F) 3
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (GL (Fin 3) F))
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Fˣ →* GL (Fin 3) F) := by
    intro u v huv
    apply Units.ext
    have := congrArg (fun g : GL (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) 0 0) huv
    simpa [GeneralLinearGroup.coe_scalar] using this
  have hcen : Nat.card (Subgroup.center (GL (Fin 3) F)) = Nat.card F - 1 := by
    rw [GeneralLinearGroup.center_eq_range_scalar,
      ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]
  change Nat.card (GL (Fin 3) F) =
    Nat.card (ProjGenLinGroup (Fin 3) F) * Nat.card (Subgroup.center (GL (Fin 3) F)) at hq
  rw [hcen, hGL, Fin.prod_univ_three] at hq
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at hq
  rw [← Nat.card_eq_fintype_card] at hq
  set r := Nat.card F
  have hr : 2 ≤ r := Finite.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (show 0 < r - 1 by omega)
  rw [← hq]
  have e1 : r ^ 3 - r = r * (r ^ 2 - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ']
  have e2 : r ^ 3 - r ^ 2 = r ^ 2 * (r - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ]
  rw [e1, e2]
  ring

end Field

theorem coprime_inner_bound {q : ℕ} (hq : Even q) (hq1 : 1 ≤ q) :
    Nat.Coprime (q ^ 3 * (q - 1)) (q + 1) := by
  obtain ⟨t, rfl⟩ := hq
  rw [← Nat.isCoprime_iff_coprime]
  push_cast [Nat.cast_sub hq1]
  refine IsCoprime.mul_left (IsCoprime.pow_left ⟨-1, 1, by ring⟩) ⟨t, 1 - t, by ring⟩

theorem coprime_field_bound {r : ℕ} (hr : Even r) (hr1 : 1 ≤ r) :
    Nat.Coprime (r ^ 3 * (r ^ 3 - 1) * (r ^ 2 - 1)) (r ^ 2 + 1) := by
  obtain ⟨s, rfl⟩ := hr
  rw [← Nat.isCoprime_iff_coprime]
  push_cast [Nat.cast_sub (Nat.one_le_pow 3 _ hr1), Nat.cast_sub (Nat.one_le_pow 2 _ hr1)]
  refine IsCoprime.mul_left (IsCoprime.mul_left (IsCoprime.pow_left ⟨-(s + s), 1, by ring⟩)
    ⟨-2 * s ^ 2 * ((s + s) - 1), 1 - 2 * s ^ 2 * (1 + (s + s) - (s + s) ^ 2), by ring⟩)
    ⟨2 * s ^ 2, 1 - 2 * s ^ 2, by ring⟩

theorem succ_dvd_card_SL_two (K : Type*) [Field K] [Finite K] :
    Nat.card K + 1 ∣ Nat.card (SpecialLinearGroup (Fin 2) K) := by
  classical
  have := Fintype.ofFinite K
  have h := Matrix.card_SL_mul_card_units (n := Fin 2) (R := K)
  rw [Matrix.card_GL_field, Fin.prod_univ_two, Nat.card_units] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [← Nat.card_eq_fintype_card] at h
  set q := Nat.card K
  have hq : 2 ≤ q := Finite.one_lt_card
  have hSL : Nat.card (SpecialLinearGroup (Fin 2) K) = (q + 1) * (q - 1) * q := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < q - 1 by omega)
    rw [h, show q ^ 2 - 1 = q ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq,
      show q ^ 2 - q = q * (q - 1) by rw [Nat.mul_sub_one, ← pow_two]]
    ring
  rw [hSL, mul_assoc]
  exact dvd_mul_right _ _

noncomputable abbrev semilinearFixed (K : Type*) [Field K] (A : GL (Fin 3) K) (σ : K ≃+* K) :
    Subgroup (projectiveSL 3 K) :=
  TauCeti.fixedSubgroup (conjAut 3 K A * fieldAut 3 K σ).toMonoidHom

theorem exists_injective_semilinearFixed_pgl {K : Type*} [Field K] [Finite K] [CharP K 2]
    (A : GL (Fin 3) K) (σ : K ≃+* K) (hσ : orderOf σ = 2)
    (hβ2 : (conjAut 3 K A * fieldAut 3 K σ) ^ 2 = 1) :
    ∃ φ : semilinearFixed K A σ →* ProjGenLinGroup (Fin 3) (fixedField K σ),
      Function.Injective φ := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    norm_num at hσ
  obtain ⟨-, -, H, hH⟩ := even_linear_field_involution_descent f.pos hK (le_refl 3) A σ hσ1 hβ2
  set C := semilinearFixed K A σ
  have hy : ∀ x ∈ C, fieldAut 3 K σ ((conjAut 3 K H)⁻¹ x) = (conjAut 3 K H)⁻¹ x := by
    intro x hx
    rw [TauCeti.mem_fixedSubgroup, MulEquiv.coe_toMonoidHom, hH, MulAut.mul_apply,
      MulAut.mul_apply] at hx
    calc fieldAut 3 K σ ((conjAut 3 K H)⁻¹ x)
        = (conjAut 3 K H)⁻¹ (conjAut 3 K H (fieldAut 3 K σ ((conjAut 3 K H)⁻¹ x))) :=
          (MulAut.inv_apply_self _ _ _).symm
      _ = (conjAut 3 K H)⁻¹ x := by rw [hx]
  set ψ : C →* ProjGenLinGroup (Fin 3) K :=
    (projToPGL 3 K).comp (((conjAut 3 K H)⁻¹).toMonoidHom.comp C.subtype)
  have hψ : ∀ x, ψ x ∈ fixedPGL (Fin 3) K σ := by
    intro x
    rw [TauCeti.mem_fixedSubgroup]
    change pglFieldAut (Fin 3) K σ (projToPGL 3 K ((conjAut 3 K H)⁻¹ x)) =
      projToPGL 3 K ((conjAut 3 K H)⁻¹ x)
    rw [← projToPGL_fieldAut, hy x x.2]
  refine ⟨(subfieldPGLEquivFixed (Fin 3) K σ).symm.toMonoidHom.comp (ψ.codRestrict _ hψ), ?_⟩
  intro x y hxy
  have h1 := (subfieldPGLEquivFixed (Fin 3) K σ).symm.injective hxy
  have h2 : ψ x = ψ y := congrArg Subtype.val h1
  have h3 := projToPGL_injective h2
  exact Subtype.ext ((conjAut 3 K H)⁻¹.injective h3)

theorem characteristic_two_linear_three_semilinear_involution_fixed_order (K : Type*) [Field K]
    [Finite K] [CharP K 2] (A : GL (Fin 3) K) (σ : K ≃+* K)
    (hβ : orderOf (conjAut 3 K A * fieldAut 3 K σ) = 2) :
    (σ = 1 ∨ orderOf σ = 2) ∧
    (σ = 1 → Nat.card (semilinearFixed K A σ) ∣ Nat.card K ^ 3 * (Nat.card K - 1)) ∧
    (orderOf σ = 2 →
      Nat.card K = Nat.card (fixedField K σ) ^ 2 ∧
      (∃ H : Subgroup (ProjGenLinGroup (Fin 3) (fixedField K σ)),
        Nonempty (semilinearFixed K A σ ≃* H)) ∧
      Nat.card (semilinearFixed K A σ) ∣ Nat.card (fixedField K σ) ^ 3 *
        (Nat.card (fixedField K σ) ^ 3 - 1) * (Nat.card (fixedField K σ) ^ 2 - 1)) ∧
    Nat.Coprime (Nat.card (semilinearFixed K A σ)) (Nat.card K + 1) ∧
    ∀ H : Subgroup (projectiveSL 3 K), H ≤ semilinearFixed K A σ →
      IsEmpty (H ≃* SpecialLinearGroup (Fin 2) K) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hqeven : Even (Nat.card K) := by
    rw [hK]
    exact Nat.even_pow.2 ⟨even_two, f.ne_zero⟩
  have hq1 : 1 ≤ Nat.card K := Finite.card_pos
  have hβ2 : (conjAut 3 K A * fieldAut 3 K σ) ^ 2 = 1 := by
    rw [← hβ]
    exact pow_orderOf_eq_one _
  have hsq : conjAut 3 K (A * GeneralLinearGroup.map (σ : K →+* K) A) * fieldAut 3 K (σ * σ) =
      1 := by
    rw [← conjAut_mul_fieldAut_mul, ← pow_two]
    exact hβ2
  obtain ⟨hσσ, -⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ _ hsq
  have hσ : σ = 1 ∨ orderOf σ = 2 := by
    have hdvd : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hσσ)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact Or.inl (orderOf_eq_one_iff.1 h)
    · exact Or.inr h
  have hcase1 : σ = 1 → Nat.card (semilinearFixed K A σ) ∣ Nat.card K ^ 3 * (Nat.card K - 1) := by
    rintro rfl
    have hA : orderOf (conjAut 3 K A) = 2 := by rwa [map_one, mul_one] at hβ
    have h := card_fixed_conjAut_dvd A hA
    simp only [semilinearFixed, map_one, mul_one]
    exact h
  have hcase2 : orderOf σ = 2 →
      Nat.card K = Nat.card (fixedField K σ) ^ 2 ∧
      (∃ H : Subgroup (ProjGenLinGroup (Fin 3) (fixedField K σ)),
        Nonempty (semilinearFixed K A σ ≃* H)) ∧
      Nat.card (semilinearFixed K A σ) ∣ Nat.card (fixedField K σ) ^ 3 *
        (Nat.card (fixedField K σ) ^ 3 - 1) * (Nat.card (fixedField K σ) ^ 2 - 1) := by
    intro h
    have hσ1 : σ ≠ 1 := by
      intro h'
      rw [h', orderOf_one] at h
      norm_num at h
    have hσ2 : σ ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one σ
    obtain ⟨φ, hφ⟩ := exists_injective_semilinearFixed_pgl A σ h hβ2
    refine ⟨fixedField_card_square K σ hσ2 hσ1, ⟨φ.range, ⟨MonoidHom.ofInjective hφ⟩⟩, ?_⟩
    rw [← card_projGenLinGroup_three]
    exact Subgroup.card_dvd_of_injective φ hφ
  have hcop : Nat.Coprime (Nat.card (semilinearFixed K A σ)) (Nat.card K + 1) := by
    rcases hσ with h | h
    · exact Nat.Coprime.coprime_dvd_left (hcase1 h) (coprime_inner_bound hqeven hq1)
    · obtain ⟨hqr, -, hdvd⟩ := hcase2 h
      have hr1 : 1 ≤ Nat.card (fixedField K σ) := Finite.card_pos
      have hreven : Even (Nat.card (fixedField K σ)) := by
        rw [hqr] at hqeven
        exact (Nat.even_pow.1 hqeven).1
      refine Nat.Coprime.coprime_dvd_left hdvd ?_
      rw [hqr]
      exact coprime_field_bound hreven hr1
  refine ⟨hσ, hcase1, hcase2, hcop, fun H hH => ⟨fun e => ?_⟩⟩
  have h1 : Nat.card K + 1 ∣ Nat.card (semilinearFixed K A σ) := by
    refine (succ_dvd_card_SL_two K).trans ?_
    rw [← Nat.card_congr e.toEquiv]
    exact Subgroup.card_dvd_of_le hH
  have h2 := (Nat.coprime_self _).1 (Nat.Coprime.coprime_dvd_left h1 hcop)
  omega

end CFSG.LocalAnalysis.SteinbergCD

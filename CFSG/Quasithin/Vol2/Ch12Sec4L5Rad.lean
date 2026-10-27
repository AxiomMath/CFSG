module

public import CFSG.Quasithin.Background.B4Statement

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

abbrev mat5 (g : ↥(StatedSL 5 (ZMod 2))) : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  ((g : Matrix.GeneralLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))

theorem mat5_mul (g h : ↥(StatedSL 5 (ZMod 2))) : mat5 (g * h) = mat5 g * mat5 h := rfl

theorem mat5_one : mat5 1 = 1 := rfl

theorem mat5_mul_inv (g : ↥(StatedSL 5 (ZMod 2))) : mat5 g * mat5 g⁻¹ = 1 := by
  rw [← mat5_mul, mul_inv_cancel, mat5_one]

theorem mul_vecMulVec' (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) (v φ : Fin 5 → ZMod 2) :
    A * Matrix.vecMulVec v φ = Matrix.vecMulVec (A *ᵥ v) φ := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem vecMulVec_mul' (B : Matrix (Fin 5) (Fin 5) (ZMod 2)) (v φ : Fin 5 → ZMod 2) :
    Matrix.vecMulVec v φ * B = Matrix.vecMulVec v (φ ᵥ* B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vecMulVec_mulVec' (v φ x : Fin 5 → ZMod 2) :
    Matrix.vecMulVec v φ *ᵥ x = (φ ⬝ᵥ x) • v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem vecMul_vecMulVec' (ψ w φ : Fin 5 → ZMod 2) :
    ψ ᵥ* Matrix.vecMulVec w φ = (ψ ⬝ᵥ w) • φ := by
  ext j
  simp only [Matrix.vecMul, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem mul_one_add_vecMulVec_mul (A B : Matrix (Fin 5) (Fin 5) (ZMod 2)) (v φ : Fin 5 → ZMod 2) :
    A * (1 + Matrix.vecMulVec v φ) * B = A * B + Matrix.vecMulVec (A *ᵥ v) (φ ᵥ* B) := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, mul_vecMulVec', vecMulVec_mul']

theorem exists_form_sep : ∀ v w : Fin 5 → ZMod 2, v ≠ 0 → w ≠ 0 → w ≠ v →
    ∃ φ : Fin 5 → ZMod 2, φ ⬝ᵥ v = 0 ∧ φ ⬝ᵥ w ≠ 0 := by
  decide +kernel

theorem one_add_vecMulVec_sq : ∀ v φ : Fin 5 → ZMod 2, φ ⬝ᵥ v = 0 →
    (1 + Matrix.vecMulVec v φ) * (1 + Matrix.vecMulVec v φ) = 1 := by
  decide +kernel

@[expose] noncomputable def radElt (v φ : Fin 5 → ZMod 2) (h : φ ⬝ᵥ v = 0) :
    ↥(StatedSL 5 (ZMod 2)) :=
  ⟨⟨1 + Matrix.vecMulVec v φ, 1 + Matrix.vecMulVec v φ, one_add_vecMulVec_sq v φ h,
      one_add_vecMulVec_sq v φ h⟩, Subgroup.subset_closure (by
    have h1 := congrArg Matrix.det (one_add_vecMulVec_sq v φ h)
    rw [Matrix.det_mul, Matrix.det_one] at h1
    have h2 : (1 + Matrix.vecMulVec v φ).det ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    show (1 + Matrix.vecMulVec v φ).det = 1
    revert h2
    generalize (1 + Matrix.vecMulVec v φ).det = a
    revert a
    decide)⟩

theorem mat5_radElt (v φ : Fin 5 → ZMod 2) (h : φ ⬝ᵥ v = 0) :
    mat5 (radElt v φ h) = 1 + Matrix.vecMulVec v φ := rfl

theorem mat5_radElt' (w φ : Fin 5 → ZMod 2) (h : φ ⬝ᵥ w = 0) :
    mat5 (radElt w φ h) = 1 + Matrix.vecMulVec w φ := rfl

theorem exists_fixed_col {S : Subgroup ↥(StatedSL 5 (ZMod 2))} (hS : IsPGroup 2 S) :
    ∃ x : Fin 5 → ZMod 2, x ≠ 0 ∧ ∀ s ∈ S, mat5 s *ᵥ x = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S (Fin 5 → ZMod 2) :=
    { smul := fun s x => mat5 s *ᵥ x
      one_smul := fun x => Matrix.one_mulVec x
      mul_smul := fun s t x => (Matrix.mulVec_mulVec x (mat5 s) (mat5 t)).symm }
  have h := hS.card_modEq_card_fixedPoints (Fin 5 → ZMod 2)
  have hcard : Nat.card (Fin 5 → ZMod 2) = 32 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rw [hcard] at h
  have h0 : (0 : Fin 5 → ZMod 2) ∈ MulAction.fixedPoints S (Fin 5 → ZMod 2) :=
    fun s => Matrix.mulVec_zero _
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints S (Fin 5 → ZMod 2)) :=
    Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 (by norm_num)))
  have hlt : 1 < Nat.card (MulAction.fixedPoints S (Fin 5 → ZMod 2)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints S (Fin 5 → ZMod 2)) :=
      Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    omega
  have hnt := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨x, hx⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints S (Fin 5 → ZMod 2))
  exact ⟨x.1, fun h => hx (Subtype.ext h), fun s hs => x.2 ⟨s, hs⟩⟩

theorem exists_fixed_row {S : Subgroup ↥(StatedSL 5 (ZMod 2))} (hS : IsPGroup 2 S) :
    ∃ x : Fin 5 → ZMod 2, x ≠ 0 ∧ ∀ s ∈ S, x ᵥ* mat5 s = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S (Fin 5 → ZMod 2) :=
    { smul := fun s x => x ᵥ* mat5 ((s⁻¹ : ↥S) : ↥(StatedSL 5 (ZMod 2)))
      one_smul := fun x => by
        show x ᵥ* mat5 ((1⁻¹ : ↥S) : ↥(StatedSL 5 (ZMod 2))) = x
        rw [inv_one]
        exact Matrix.vecMul_one x
      mul_smul := fun s t x => by
        show x ᵥ* mat5 (((s * t)⁻¹ : ↥S) : ↥(StatedSL 5 (ZMod 2))) =
          (x ᵥ* mat5 ((t⁻¹ : ↥S) : ↥(StatedSL 5 (ZMod 2)))) ᵥ*
            mat5 ((s⁻¹ : ↥S) : ↥(StatedSL 5 (ZMod 2)))
        rw [mul_inv_rev, Matrix.vecMul_vecMul]
        rfl }
  have h := hS.card_modEq_card_fixedPoints (Fin 5 → ZMod 2)
  have hcard : Nat.card (Fin 5 → ZMod 2) = 32 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rw [hcard] at h
  have h0 : (0 : Fin 5 → ZMod 2) ∈ MulAction.fixedPoints S (Fin 5 → ZMod 2) :=
    fun s => Matrix.zero_vecMul _
  have h2 : 2 ∣ Nat.card (MulAction.fixedPoints S (Fin 5 → ZMod 2)) :=
    Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 (by norm_num)))
  have hlt : 1 < Nat.card (MulAction.fixedPoints S (Fin 5 → ZMod 2)) := by
    have hpos : 0 < Nat.card (MulAction.fixedPoints S (Fin 5 → ZMod 2)) :=
      Nat.card_pos_iff.2 ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
    omega
  have hnt := Finite.one_lt_card_iff_nontrivial.1 hlt
  obtain ⟨x, hx⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints S (Fin 5 → ZMod 2))
  refine ⟨x.1, fun h => hx (Subtype.ext h), fun s hs => ?_⟩
  have h1 : x.1 ᵥ* mat5 (((⟨s, hs⟩ : ↥S)⁻¹⁻¹ : ↥S) : ↥(StatedSL 5 (ZMod 2))) = x.1 :=
    x.2 (⟨s, hs⟩ : ↥S)⁻¹
  rwa [inv_inv] at h1

theorem le_normalizer_of_isEndNodeRadical5 {R S : Subgroup ↥(StatedSL 5 (ZMod 2))}
    (hR : IsEndNodeRadical5 R) (hS : IsPGroup 2 S) (hRS : R ≤ S) :
    S ≤ Subgroup.normalizer (R : Set ↥(StatedSL 5 (ZMod 2))) := by
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hnorm : (∀ s ∈ S, ∀ g ∈ R, s * g * s⁻¹ ∈ R) →
      S ≤ Subgroup.normalizer (R : Set ↥(StatedSL 5 (ZMod 2))) := by
    intro key s hs
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key s hs g, fun hg => ?_⟩
    have h1 := key s⁻¹ (S.inv_mem hs) _ hg
    rwa [show s⁻¹ * (s * g * s⁻¹) * s⁻¹⁻¹ = g by group] at h1
  rcases hR with ⟨v, hv, hRv⟩ | ⟨φ, hφ, hRφ⟩
  ·
    obtain ⟨x, hx0, hxS⟩ := exists_fixed_col hS
    have hxv : x = v := by
      by_contra hne
      obtain ⟨ψ, hψv, hψx⟩ := exists_form_sep v x hv hx0 hne
      have hg : radElt v ψ hψv ∈ R := (hRv _).2 ⟨ψ, hψv, rfl⟩
      have h1 := hxS _ (hRS hg)
      rw [mat5_radElt, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec'] at h1
      have h2 : (ψ ⬝ᵥ x) • v = 0 := add_eq_left.1 h1
      rcases hcases (ψ ⬝ᵥ x) with h3 | h3
      · exact hψx h3
      · rw [h3, one_smul] at h2
        exact hv h2
    have hvS : ∀ s ∈ S, mat5 s *ᵥ v = v := fun s hs => by rw [← hxv]; exact hxS s hs
    refine hnorm fun s hs g hg => ?_
    obtain ⟨ψ, hψ, hgψ⟩ := (hRv g).1 hg
    have hgψ' : mat5 g = 1 + Matrix.vecMulVec v ψ := hgψ
    refine (hRv _).2 ⟨ψ ᵥ* mat5 s⁻¹, ?_, ?_⟩
    · rw [← Matrix.dotProduct_mulVec, hvS _ (S.inv_mem hs), hψ]
    · show mat5 (s * g * s⁻¹) = _
      rw [mat5_mul, mat5_mul, hgψ', mul_one_add_vecMulVec_mul, mat5_mul_inv, hvS s hs]
  ·
    obtain ⟨x, hx0, hxS⟩ := exists_fixed_row hS
    have hxφ : x = φ := by
      by_contra hne
      obtain ⟨w, hwφ, hwx⟩ := exists_form_sep φ x hφ hx0 hne
      have hwφ' : φ ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hwφ
      have hg : radElt w φ hwφ' ∈ R := (hRφ _).2 ⟨w, hwφ', rfl⟩
      have h1 := hxS _ (hRS hg)
      rw [mat5_radElt, Matrix.vecMul_add, Matrix.vecMul_one, vecMul_vecMulVec'] at h1
      have h2 : (x ⬝ᵥ w) • φ = 0 := add_eq_left.1 h1
      have hxw : x ⬝ᵥ w ≠ 0 := by rw [dotProduct_comm]; exact hwx
      rcases hcases (x ⬝ᵥ w) with h3 | h3
      · exact hxw h3
      · rw [h3, one_smul] at h2
        exact hφ h2
    have hφS : ∀ s ∈ S, φ ᵥ* mat5 s = φ := fun s hs => by rw [← hxφ]; exact hxS s hs
    refine hnorm fun s hs g hg => ?_
    obtain ⟨w, hw, hgw⟩ := (hRφ g).1 hg
    have hgw' : mat5 g = 1 + Matrix.vecMulVec w φ := hgw
    refine (hRφ _).2 ⟨mat5 s *ᵥ w, ?_, ?_⟩
    · rw [Matrix.dotProduct_mulVec, hφS s hs, hw]
    · show mat5 (s * g * s⁻¹) = _
      rw [mat5_mul, mat5_mul, hgw', mul_one_add_vecMulVec_mul, mat5_mul_inv,
        hφS _ (S.inv_mem hs)]

end CFSG.Quasithin.H13
